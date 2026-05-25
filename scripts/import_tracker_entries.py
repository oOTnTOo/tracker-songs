#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
import_tracker_entries.py

Import multiple video IDs and their comment-style timelines into the tracker Git database.

Key rules:
  - Database uses generic field "id"; the stored value has no platform prefix.
  - Archive ID field is "ad".
  - Content ID field is "cd".
  - Long original video title is not stored in track rows.
  - No m3u is generated.
  - Existing shards are rebuilt automatically.
  - Timeline parsing accepts both:
      00:00 Song
      Song 00:00
      Song00:00
      01. 00:00 Song
      01. Song 00:00
      3分54秒 Song
      Song 3分54秒
    But a line is imported only when it has a unique, unambiguous parse.

Examples:

  python scripts/import_tracker_entries.py --root . --input new_items.txt

  python scripts/import_tracker_entries.py --root . --input new_items.json --cookie-file cookie.txt

Text input format:

  # BV1FYLu6iE9L
  artist: Aaliyah
  album: I Care 4 U
  00:00 Back & Forth
  03:50 Are You That Somebody?
  Rock The Boat 01:03:25

  # BV1dTLw6gEZX
  00:00 Marigold & Patchwork
  Antihero 05:50

JSON input format:

  [
    {
      "id": "BV1FYLu6iE9L",
      "artist": "Aaliyah",
      "album": "I Care 4 U",
      "comment": "00:00 Back & Forth\n03:50 Are You That Somebody?"
    }
  ]
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import hashlib
import json
import os
import re
import shutil
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple


DEFAULT_SHARD_SIZE = 700_000
DEFAULT_TIMEOUT = 15
USER_AGENT = "tracker-songs-importer/1.0 (local script)"


# ---------------------------------------------------------------------------
# Data models
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class ImportEntry:
    id: str
    comment: str
    artist: str = ""
    album: str = ""
    album_artist: str = ""
    title_hint: str = ""


@dataclasses.dataclass(frozen=True)
class ParsedTrack:
    start: int
    title: str
    source_line: str
    mode: str


@dataclasses.dataclass
class VideoInfo:
    id: str
    ad: str = ""
    cd: str = ""
    title: str = ""


@dataclasses.dataclass
class ImportIssue:
    id: str
    type: str
    message: str
    line: str = ""


# ---------------------------------------------------------------------------
# Basic helpers
# ---------------------------------------------------------------------------

def strip_platform_prefix(value: str) -> str:
    value = (value or "").strip()
    if value.startswith("BV"):
        return value[2:]
    return value


def to_platform_id(value: str) -> str:
    value = (value or "").strip()
    if value.startswith("BV"):
        return value
    return "BV" + value


def stable_json(obj: Any, pretty: bool = False) -> str:
    if pretty:
        return json.dumps(obj, ensure_ascii=False, indent=2)
    return json.dumps(obj, ensure_ascii=False, separators=(",", ":"))


def safe_filename(s: str, max_len: int = 96) -> str:
    s = re.sub(r'[\\/:*?"<>|\r\n\t]+', "_", s or "")
    s = re.sub(r"\s+", " ", s).strip(" ._")
    if not s:
        s = "unknown"
    return s[:max_len]


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8-sig", errors="replace")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def urlencode_component(value: str) -> str:
    return urllib.parse.quote(str(value), safe="")


def make_track_url(track: Dict[str, Any]) -> str:
    query = [
        ("start", track.get("start", 0)),
        ("end", track.get("end", -1)),
        ("title", track.get("title", "")),
        ("artist", track.get("artist", "")),
        ("album", track.get("album", "")),
    ]

    if track.get("ad"):
        query.append(("ad", track["ad"]))

    if track.get("cd"):
        query.append(("cd", track["cd"]))

    query_text = "&".join(f"{k}={urlencode_component(v)}" for k, v in query)
    return f"bl://track/{track['id']}?{query_text}"


def http_get_json(url: str, headers: Optional[Dict[str, str]] = None, timeout: int = DEFAULT_TIMEOUT) -> Dict[str, Any]:
    req_headers = {
        "User-Agent": USER_AGENT,
        "Accept": "application/json,text/plain,*/*",
    }

    if headers:
        req_headers.update(headers)

    req = urllib.request.Request(url, headers=req_headers, method="GET")

    with urllib.request.urlopen(req, timeout=timeout) as resp:
        data = resp.read()

    return json.loads(data.decode("utf-8", errors="replace"))


# ---------------------------------------------------------------------------
# Timeline parsing
# ---------------------------------------------------------------------------

# Supported:
#   00:00
#   03:54
#   01:03:25
#   3分54秒
#   54秒
#
# The regex intentionally does not include surrounding title text.
TIME_RE = re.compile(
    r"""
    (?<!\d)
    (?:
        (?P<h>\d{1,2})[:：](?P<m>[0-5]?\d)[:：](?P<s>[0-5]\d)
        |
        (?P<m2>\d{1,3})[:：](?P<s2>[0-5]\d)
        |
        (?P<cm>\d{1,3})\s*分\s*(?P<cs>[0-5]?\d)\s*秒
        |
        (?P<onlys>\d{1,4})\s*秒
    )
    (?!\d)
    """,
    re.VERBOSE,
)

ENTRY_DELIMS = r"\s\-–—:：、，,;.．。|/\\_~·•*#\[\]【】（）()<>《》"
ORDER_PREFIX_RE = re.compile(
    r"""
    ^\s*
    (?:
        [\-\–\—\*\•]+\s*
        |
        (?:track|trk|no\.?|song|第)\s*\d{1,3}\s*(?:首|曲)?\s*[\.\)、\)\]\-–—_:：]?\s*
        |
        cd\s*\d+\s*[-_ ]+\s*\d{1,3}\s*[\.\)、\)\]\-–—_:：]?\s*
        |
        disc\s*\d+\s*[-_ ]+\s*\d{1,3}\s*[\.\)、\)\]\-–—_:：]?\s*
        |
        [a-zA-Z]\d{1,2}\s*[\.\)、\)\]\-–—_:：]\s*
        |
        \d{1,3}\s*[\.\)、\)\]\-–—_:：]\s*
    )+
    """,
    re.IGNORECASE | re.VERBOSE,
)

ORDER_SUFFIX_RE = re.compile(
    r"""
    (?:\s+
        (?:
            \d{1,3}\s*[\.\)、\)\]\-–—_:：]
            |
            track\s*\d{1,3}\s*[\.\)、\)\]\-–—_:：]?
        )
    )\s*$
    """,
    re.IGNORECASE | re.VERBOSE,
)


def parse_time_to_seconds(match: re.Match[str]) -> int:
    if match.group("h") is not None:
        h = int(match.group("h"))
        m = int(match.group("m"))
        s = int(match.group("s"))
        return h * 3600 + m * 60 + s

    if match.group("m2") is not None:
        m = int(match.group("m2"))
        s = int(match.group("s2"))
        return m * 60 + s

    if match.group("cm") is not None:
        m = int(match.group("cm"))
        s = int(match.group("cs"))
        return m * 60 + s

    return int(match.group("onlys"))


def clean_title(title: str) -> str:
    title = title or ""
    title = title.replace("\u3000", " ")
    title = re.sub(r"\s+", " ", title)
    title = title.strip(" \t\r\n-–—:：、，,;.．。|/\\_~·•*#[]【】()（）<>《》")

    # Remove timestamps accidentally left around the title.
    title = TIME_RE.sub("", title)
    title = re.sub(r"\s+", " ", title).strip()

    # Remove clear track ordering, but preserve titles like "16 Days".
    old = None
    while old != title:
        old = title
        title = ORDER_PREFIX_RE.sub("", title).strip()
        title = ORDER_SUFFIX_RE.sub("", title).strip()

    title = title.strip(" \t\r\n-–—:：、，,;.．。|/\\_~·•*#[]【】()（）<>《》")
    return title


def looks_like_separator_text(text: str) -> bool:
    text = text or ""
    if not text.strip():
        return True

    # Allow list markers before a timestamp, e.g. "01. 00:00 Song".
    text2 = ORDER_PREFIX_RE.sub("", text)
    return not text2.strip(" " + ENTRY_DELIMS)


def trim_segment_for_title(text: str) -> str:
    text = text or ""
    text = re.sub(r"^[\s" + re.escape(ENTRY_DELIMS) + r"]+", "", text)
    text = re.sub(r"[\s" + re.escape(ENTRY_DELIMS) + r"]+$", "", text)
    return clean_title(text)


def find_time_matches(line: str) -> List[re.Match[str]]:
    return list(TIME_RE.finditer(line))


def parse_line_time_first(line: str) -> List[ParsedTrack]:
    matches = find_time_matches(line)
    if not matches:
        return []

    out: List[ParsedTrack] = []

    for i, m in enumerate(matches):
        prefix_start = matches[i - 1].end() if i > 0 else 0
        prefix = line[prefix_start:m.start()]

        # A time-first item must have only separators/list markers before the time
        # inside its local segment.
        if not looks_like_separator_text(prefix):
            return []

        next_start = matches[i + 1].start() if i + 1 < len(matches) else len(line)
        raw_title = line[m.end():next_start]
        title = trim_segment_for_title(raw_title)

        if not title:
            return []

        out.append(
            ParsedTrack(
                start=parse_time_to_seconds(m),
                title=title,
                source_line=line,
                mode="time_first",
            )
        )

    return out


def parse_line_title_first(line: str) -> List[ParsedTrack]:
    matches = find_time_matches(line)
    if not matches:
        return []

    out: List[ParsedTrack] = []

    for i, m in enumerate(matches):
        segment_start = matches[i - 1].end() if i > 0 else 0
        raw_title = line[segment_start:m.start()]
        title = trim_segment_for_title(raw_title)

        if not title:
            return []

        out.append(
            ParsedTrack(
                start=parse_time_to_seconds(m),
                title=title,
                source_line=line,
                mode="title_first",
            )
        )

    return out


def tracks_signature(tracks: List[ParsedTrack]) -> List[Tuple[int, str]]:
    return [(t.start, t.title) for t in tracks]


def parse_timeline_comment(comment: str, video_id: str = "") -> Tuple[List[ParsedTrack], List[ImportIssue]]:
    """
    Parse a timeline comment.

    A line is accepted only if exactly one parse direction is valid:
      - time-first
      - title-first

    If both directions are valid but produce different results, the line is considered
    ambiguous and skipped.
    """
    tracks: List[ParsedTrack] = []
    issues: List[ImportIssue] = []

    # Normalize common inline separators into line breaks only when they separate
    # obvious list items. We avoid aggressive splitting to prevent false positives.
    text = comment.replace("\r\n", "\n").replace("\r", "\n")
    raw_lines = []
    for line in text.split("\n"):
        line = line.strip()
        if not line:
            continue

        # Some comments use " / " or " | " between complete time-first items.
        # Split only if the separator is followed by a timestamp.
        pieces = re.split(r"\s+(?:/|\|)\s+(?=(?:\d{1,2}[:：])|\d{1,3}\s*分)", line)
        raw_lines.extend(p.strip() for p in pieces if p.strip())

    for line in raw_lines:
        tf = parse_line_time_first(line)
        rf = parse_line_title_first(line)

        if tf and not rf:
            tracks.extend(tf)
            continue

        if rf and not tf:
            tracks.extend(rf)
            continue

        if tf and rf:
            if tracks_signature(tf) == tracks_signature(rf):
                tracks.extend(tf)
            else:
                issues.append(
                    ImportIssue(
                        id=video_id,
                        type="ambiguous_line",
                        message="line can be parsed in multiple incompatible ways; skipped",
                        line=line,
                    )
                )
            continue

        # No valid parse. Only record lines that contain something that looks like a time.
        if TIME_RE.search(line):
            issues.append(
                ImportIssue(
                    id=video_id,
                    type="unparsed_line",
                    message="line contains a timestamp but has no unique track title parse",
                    line=line,
                )
            )

    # Remove duplicated starts only when they agree on the title.
    by_start: Dict[int, List[ParsedTrack]] = collections.defaultdict(list)
    for t in tracks:
        by_start[t.start].append(t)

    deduped: List[ParsedTrack] = []
    for start, group in by_start.items():
        titles = {g.title for g in group}
        if len(titles) > 1:
            issues.append(
                ImportIssue(
                    id=video_id,
                    type="duplicate_start_conflict",
                    message=f"same start second has multiple titles: {sorted(titles)}; skipped",
                    line=" | ".join(g.source_line for g in group[:3]),
                )
            )
            continue

        deduped.append(group[0])

    deduped.sort(key=lambda x: x.start)

    # Ensure strictly increasing start times.
    final: List[ParsedTrack] = []
    last = -1
    for t in deduped:
        if t.start <= last:
            issues.append(
                ImportIssue(
                    id=video_id,
                    type="non_increasing_start",
                    message="track start seconds are not strictly increasing; skipped",
                    line=t.source_line,
                )
            )
            continue
        final.append(t)
        last = t.start

    return final, issues


# ---------------------------------------------------------------------------
# Input parser
# ---------------------------------------------------------------------------

ID_RE = re.compile(r"(?<![A-Za-z0-9])(?:BV)?([A-Za-z0-9]{8,14})(?![A-Za-z0-9])")


def parse_json_input(path: Path) -> List[ImportEntry]:
    data = json.loads(read_text(path))
    if isinstance(data, dict):
        data = [data]

    entries: List[ImportEntry] = []
    for obj in data:
        if not isinstance(obj, dict):
            continue

        raw_id = str(obj.get("id") or obj.get("bvid") or obj.get("bv") or "").strip()
        if not raw_id:
            continue

        comment = str(obj.get("comment") or obj.get("timeline") or obj.get("text") or "").strip()
        if not comment and isinstance(obj.get("tracks"), list):
            lines = []
            for t in obj["tracks"]:
                if isinstance(t, dict):
                    start = t.get("time") or t.get("start_text") or t.get("start") or ""
                    title = t.get("title") or t.get("song") or ""
                    lines.append(f"{start} {title}".strip())
            comment = "\n".join(lines)

        entries.append(
            ImportEntry(
                id=strip_platform_prefix(raw_id),
                comment=comment,
                artist=str(obj.get("artist") or "").strip(),
                album=str(obj.get("album") or "").strip(),
                album_artist=str(obj.get("album_artist") or obj.get("artist") or "").strip(),
                title_hint=str(obj.get("video_title") or obj.get("title_hint") or "").strip(),
            )
        )

    return entries


def parse_text_input(path: Path) -> List[ImportEntry]:
    text = read_text(path)
    entries: List[ImportEntry] = []
    current: Optional[Dict[str, Any]] = None

    def flush() -> None:
        nonlocal current
        if not current:
            return

        comment = "\n".join(current.get("lines", [])).strip()
        if current.get("id") and comment:
            entries.append(
                ImportEntry(
                    id=strip_platform_prefix(current["id"]),
                    comment=comment,
                    artist=current.get("artist", ""),
                    album=current.get("album", ""),
                    album_artist=current.get("album_artist", "") or current.get("artist", ""),
                    title_hint=current.get("title_hint", ""),
                )
            )
        current = None

    for raw_line in text.splitlines():
        line = raw_line.rstrip("\n")
        stripped = line.strip()

        if not stripped:
            if current is not None:
                current.setdefault("lines", []).append("")
            continue

        # Section header:
        #   # BVxxxx
        #   [BVxxxx]
        #   id: BVxxxx
        #   BVxxxx
        #   BVxxxx<TAB>timeline...
        header_match = None

        if stripped.startswith("#"):
            header_match = ID_RE.search(stripped[1:].strip())
            header_rest = ""
            if header_match:
                header_rest = stripped[1:].strip()[header_match.end():].strip()
        elif stripped.startswith("[") and stripped.endswith("]"):
            header_match = ID_RE.search(stripped)
            header_rest = ""
        elif re.match(r"^(id|bv|bvid)\s*[:=]", stripped, re.IGNORECASE):
            possible = re.split(r"[:=]", stripped, 1)[1].strip()
            header_match = ID_RE.search(possible)
            header_rest = possible[header_match.end():].strip() if header_match else ""
        else:
            # A raw ID at the beginning of the line can start a new entry.
            m = ID_RE.match(stripped)
            if m:
                tail = stripped[m.end():].strip()
                # Treat as a header if tail is empty, a tab-separated comment, or tail contains a timestamp.
                if not tail or "\t" in line or TIME_RE.search(tail):
                    header_match = m
                    header_rest = tail.lstrip("\t ").strip()
                else:
                    header_match = None

        if header_match:
            flush()
            current = {"id": header_match.group(1), "lines": []}
            if header_rest:
                current["lines"].append(header_rest)
            continue

        if current is None:
            # Ignore lines before the first ID section.
            continue

        meta = re.match(r"^(artist|album|album_artist|title_hint)\s*[:=]\s*(.+)$", stripped, re.IGNORECASE)
        if meta:
            key = meta.group(1).lower()
            current[key] = meta.group(2).strip()
            continue

        current.setdefault("lines", []).append(line)

    flush()
    return entries


def load_import_entries(path: Path) -> List[ImportEntry]:
    text = read_text(path).lstrip()
    if text.startswith("[") or text.startswith("{"):
        return parse_json_input(path)
    return parse_text_input(path)


# ---------------------------------------------------------------------------
# Online metadata enrichment
# ---------------------------------------------------------------------------

def fetch_video_info(video_id: str, cookie: str = "", no_network: bool = False) -> Tuple[VideoInfo, Optional[str]]:
    video_id = strip_platform_prefix(video_id)
    info = VideoInfo(id=video_id)

    if no_network:
        return info, "network disabled"

    url = "https://api.bilibili.com/x/web-interface/view?bvid=" + urllib.parse.quote(to_platform_id(video_id))

    headers: Dict[str, str] = {
        "Referer": "https://www.bilibili.com/video/" + to_platform_id(video_id) + "/",
    }

    if cookie:
        headers["Cookie"] = cookie

    try:
        obj = http_get_json(url, headers=headers)
    except Exception as e:
        return info, f"view api request failed: {e}"

    if obj.get("code") != 0:
        return info, f"view api returned code={obj.get('code')} message={obj.get('message')}"

    data = obj.get("data") or {}
    info.ad = str(data.get("aid") or "")
    info.title = str(data.get("title") or "")

    pages = data.get("pages") or []
    if pages and isinstance(pages[0], dict):
        info.cd = str(pages[0].get("cid") or "")

    return info, None


TITLE_PATTERNS = [
    # Aaliyah2002年发行专辑《I Care 4 U》...
    re.compile(r"^\s*(?P<artist>.+?)(?:19|20)\d{2}\s*年.*?(?:专辑|EP|单曲|唱片)[《<](?P<album>[^》>]+)[》>]", re.I),
    # Artist - Album
    re.compile(r"^\s*(?P<artist>[^《》\[\]【】]{1,80}?)\s*[-–—]\s*(?P<album>[^《》\[\]【】]{1,100})(?:\s*[\[【(（]|$)", re.I),
    # Artist《Album》
    re.compile(r"^\s*(?P<artist>[^《》]{1,80}?)[《<](?P<album>[^》>]+)[》>]", re.I),
]


def infer_from_video_title(video_title: str) -> Tuple[str, str]:
    title = video_title or ""
    for pat in TITLE_PATTERNS:
        m = pat.search(title)
        if m:
            artist = clean_title(m.group("artist"))
            album = clean_title(m.group("album"))
            if artist and album:
                return artist, album
    return "", ""


def _artist_credit_name(credit: Any) -> str:
    if not credit:
        return ""

    if isinstance(credit, list):
        parts: List[str] = []
        for item in credit:
            if isinstance(item, dict):
                artist_obj = item.get("artist") or {}
                name = artist_obj.get("name") or item.get("name") or ""
                joinphrase = item.get("joinphrase") or ""
                if name:
                    parts.append(str(name) + str(joinphrase))
        return "".join(parts).strip()

    if isinstance(credit, dict):
        artist_obj = credit.get("artist") or {}
        return str(artist_obj.get("name") or credit.get("name") or "").strip()

    return ""


def musicbrainz_vote(track_titles: List[str], timeout: int = DEFAULT_TIMEOUT) -> collections.Counter:
    """
    Vote for (track_artist, album, album_artist).

    MusicBrainz distinguishes recording artist and release artist-credit.
    For album_artist we prefer release["artist-credit"], and fall back to the
    recording artist when release artist is missing.
    """
    votes: collections.Counter = collections.Counter()

    for title in track_titles[:8]:
        q = f'recording:"{title}"'
        url = "https://musicbrainz.org/ws/2/recording/?" + urllib.parse.urlencode({
            "query": q,
            "fmt": "json",
            "limit": "5",
            "inc": "artist-credits+releases",
        })

        try:
            obj = http_get_json(url, timeout=timeout)
        except Exception:
            continue

        for rec in obj.get("recordings", []) or []:
            track_artist = _artist_credit_name(rec.get("artist-credit"))
            releases = rec.get("releases") or []

            for release in releases[:3]:
                if not isinstance(release, dict):
                    continue

                album = str(release.get("title") or "").strip()
                album_artist = _artist_credit_name(release.get("artist-credit")) or track_artist

                if track_artist and album and album_artist:
                    # MusicBrainz is weighted higher because it has explicit release artist-credit.
                    votes[(track_artist, album, album_artist)] += 3

        time.sleep(0.35)

    return votes


def itunes_vote(track_titles: List[str], timeout: int = DEFAULT_TIMEOUT) -> collections.Counter:
    """
    Vote for (track_artist, album, album_artist).

    iTunes usually provides artistName and collectionName. Some results also
    provide collectionArtistName; when it is missing, use artistName as fallback.
    """
    votes: collections.Counter = collections.Counter()

    for title in track_titles[:8]:
        url = "https://itunes.apple.com/search?" + urllib.parse.urlencode({
            "term": title,
            "media": "music",
            "entity": "song",
            "limit": "5",
        })

        try:
            obj = http_get_json(url, timeout=timeout)
        except Exception:
            continue

        for item in obj.get("results", []) or []:
            track_artist = str(item.get("artistName") or "").strip()
            album = str(item.get("collectionName") or "").strip()
            album_artist = str(item.get("collectionArtistName") or "").strip() or track_artist

            if track_artist and album and album_artist:
                votes[(track_artist, album, album_artist)] += 1

        time.sleep(0.1)

    return votes


def _choose_best_metadata_vote(
    votes: collections.Counter,
    preferred_artist: str = "",
    preferred_album: str = "",
    preferred_album_artist: str = "",
) -> Tuple[str, str, str]:
    if not votes:
        return "", "", ""

    def score_item(item: Tuple[Tuple[str, str, str], int]) -> Tuple[int, int]:
        (artist, album, album_artist), score = item
        bonus = 0

        if preferred_artist and artist.lower() == preferred_artist.lower():
            bonus += 4

        if preferred_album and album.lower() == preferred_album.lower():
            bonus += 4

        if preferred_album_artist and album_artist.lower() == preferred_album_artist.lower():
            bonus += 4

        # Prefer non-compilation-looking album artists when scores tie.
        if album_artist and album_artist.lower() not in {"various artists", "various", "群星"}:
            bonus += 1

        return score + bonus, score

    (artist, album, album_artist), _score = max(votes.items(), key=score_item)
    return artist, album, album_artist


def infer_artist_album_artist_album(
    entry: ImportEntry,
    parsed_tracks: List[ParsedTrack],
    video_info: VideoInfo,
    no_network: bool = False,
    timeout: int = DEFAULT_TIMEOUT,
) -> Tuple[str, str, str]:
    """
    Infer track artist, album, and album artist.

    Priority:
      1. Explicit user-provided artist / album / album_artist.
      2. Artist + album parsed from the original video title.
      3. Multi-track voting from online song searches.
      4. Safe fallback values.

    Even when artist/album are found from the video title, this function still
    queries song databases to fill album_artist if it is missing.
    """
    artist = entry.artist.strip()
    album = entry.album.strip()
    album_artist = entry.album_artist.strip()

    title_source = entry.title_hint or video_info.title
    title_artist, title_album = infer_from_video_title(title_source)

    if not artist:
        artist = title_artist

    if not album:
        album = title_album

    titles = [t.title for t in parsed_tracks if t.title][:10]
    votes: collections.Counter = collections.Counter()

    should_query = not no_network and titles and (
        not artist or not album or not album_artist
    )

    if should_query:
        votes.update(musicbrainz_vote(titles, timeout=timeout))
        votes.update(itunes_vote(titles, timeout=timeout))

    v_artist, v_album, v_album_artist = _choose_best_metadata_vote(
        votes,
        preferred_artist=artist,
        preferred_album=album,
        preferred_album_artist=album_artist,
    )

    if not artist:
        artist = v_artist

    if not album:
        album = v_album

    if not album_artist:
        # Prefer explicit album artist from online release metadata.
        album_artist = v_album_artist

    if not album_artist:
        # If online sources are unavailable, album artist usually equals album-level artist.
        album_artist = artist

    return (
        artist or "Unknown Artist",
        album or "Unknown Album",
        album_artist or artist or "Unknown Artist",
    )


# Backward-compatible wrapper for older local callers.
def infer_artist_album(
    entry: ImportEntry,
    parsed_tracks: List[ParsedTrack],
    video_info: VideoInfo,
    no_network: bool = False,
    timeout: int = DEFAULT_TIMEOUT,
) -> Tuple[str, str]:
    artist, album, _album_artist = infer_artist_album_artist_album(
        entry=entry,
        parsed_tracks=parsed_tracks,
        video_info=video_info,
        no_network=no_network,
        timeout=timeout,
    )
    return artist, album

    titles = [t.title for t in parsed_tracks if t.title][:10]
    votes: collections.Counter = collections.Counter()
    votes.update(musicbrainz_vote(titles, timeout=timeout))
    votes.update(itunes_vote(titles, timeout=timeout))

    if votes:
        (v_artist, v_album), _ = votes.most_common(1)[0]
        artist = artist or v_artist
        album = album or v_album

    return artist or "Unknown Artist", album or "Unknown Album"


# ---------------------------------------------------------------------------
# Database load / rebuild
# ---------------------------------------------------------------------------

def load_existing_tracks(root: Path) -> List[Dict[str, Any]]:
    tracks_dir = root / "data" / "tracks"
    all_tracks: List[Dict[str, Any]] = []

    if tracks_dir.exists():
        for path in sorted(tracks_dir.glob("*.jsonl")):
            for line in read_text(path).splitlines():
                if not line.strip():
                    continue
                try:
                    obj = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if isinstance(obj, dict):
                    all_tracks.append(normalize_existing_track(obj))
        return all_tracks

    single = root / "data" / "tracks.jsonl"
    if single.exists():
        for line in read_text(single).splitlines():
            if not line.strip():
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(obj, dict):
                all_tracks.append(normalize_existing_track(obj))

    return all_tracks


def normalize_existing_track(obj: Dict[str, Any]) -> Dict[str, Any]:
    # Keep compatibility with older generated packages.
    if "id" not in obj:
        if obj.get("bvid"):
            obj["id"] = strip_platform_prefix(str(obj.get("bvid")))
        elif obj.get("bv"):
            obj["id"] = strip_platform_prefix(str(obj.get("bv")))

    if "ad" not in obj and obj.get("avid"):
        obj["ad"] = str(obj.get("avid"))

    if "cd" not in obj and obj.get("cid"):
        obj["cd"] = str(obj.get("cid"))

    obj.pop("bvid", None)
    obj.pop("bv", None)
    obj.pop("avid", None)
    obj.pop("cid", None)
    obj.pop("video_title", None)

    obj["id"] = strip_platform_prefix(str(obj.get("id") or ""))

    if "url" not in obj or not obj["url"]:
        obj["url"] = make_track_url(obj)

    return obj


def build_tracks_for_entry(
    entry: ImportEntry,
    cookie: str,
    no_network: bool,
    timeout: int,
    issues: List[ImportIssue],
) -> List[Dict[str, Any]]:
    entry.id = strip_platform_prefix(entry.id)

    parsed, parse_issues = parse_timeline_comment(entry.comment, entry.id)
    issues.extend(parse_issues)

    if not parsed:
        issues.append(
            ImportIssue(
                id=entry.id,
                type="no_tracks",
                message="no uniquely parsed timeline tracks",
            )
        )
        return []

    video_info, video_error = fetch_video_info(entry.id, cookie=cookie, no_network=no_network)
    if video_error:
        issues.append(
            ImportIssue(
                id=entry.id,
                type="video_info",
                message=video_error,
            )
        )

    artist, album, album_artist = infer_artist_album_artist_album(
        entry=entry,
        parsed_tracks=parsed,
        video_info=video_info,
        no_network=no_network,
        timeout=timeout,
    )

    result: List[Dict[str, Any]] = []

    for i, item in enumerate(parsed):
        end = parsed[i + 1].start if i + 1 < len(parsed) else -1

        track: Dict[str, Any] = {
            "id": entry.id,
            "start": item.start,
            "end": end,
            "title": item.title,
            "artist": artist,
            "album": album,
            "album_artist": album_artist,
        }

        if video_info.ad:
            track["ad"] = video_info.ad

        if video_info.cd:
            track["cd"] = video_info.cd

        # Stable field order.
        ordered: Dict[str, Any] = {
            "id": track["id"],
        }
        if track.get("ad"):
            ordered["ad"] = track["ad"]
        if track.get("cd"):
            ordered["cd"] = track["cd"]

        ordered.update({
            "start": track["start"],
            "end": track["end"],
            "title": track["title"],
            "artist": track["artist"],
            "album": track["album"],
            "album_artist": track["album_artist"],
        })

        ordered["url"] = make_track_url(ordered)
        result.append(ordered)

    return result


def merge_tracks(existing: List[Dict[str, Any]], incoming: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    merged: Dict[Tuple[str, int], Dict[str, Any]] = {}

    for t in existing:
        key = (str(t.get("id") or ""), int(t.get("start") or 0))
        if key[0]:
            merged[key] = t

    for t in incoming:
        key = (str(t.get("id") or ""), int(t.get("start") or 0))
        if key[0]:
            merged[key] = t

    result = list(merged.values())
    result.sort(
        key=lambda x: (
            str(x.get("artist") or ""),
            str(x.get("album") or ""),
            str(x.get("id") or ""),
            int(x.get("start") or 0),
        )
    )
    return result


def rebuild_shards(root: Path, tracks: List[Dict[str, Any]], shard_size: int) -> None:
    tracks_dir = root / "data" / "tracks"
    if tracks_dir.exists():
        shutil.rmtree(tracks_dir)
    tracks_dir.mkdir(parents=True, exist_ok=True)

    manifest = {
        "schema": 2,
        "kind": "tracker-songs-sharded-jsonl",
        "total_tracks": len(tracks),
        "shard_size_target": shard_size,
        "shards": [],
    }

    shard_index = 0
    current_lines: List[str] = []
    current_size = 0
    current_count = 0

    def flush() -> None:
        nonlocal shard_index, current_lines, current_size, current_count

        if not current_lines:
            return

        name = f"tracks_{shard_index:03d}.jsonl"
        rel = f"data/tracks/{name}"
        path = root / rel

        data = ("\n".join(current_lines) + "\n").encode("utf-8")
        path.write_bytes(data)

        manifest["shards"].append({
            "path": rel,
            "tracks": current_count,
            "bytes": len(data),
            "sha256": sha256_bytes(data),
        })

        shard_index += 1
        current_lines = []
        current_size = 0
        current_count = 0

    for track in tracks:
        line = stable_json(track)
        line_size = len(line.encode("utf-8")) + 1

        if current_lines and current_size + line_size > shard_size:
            flush()

        current_lines.append(line)
        current_size += line_size
        current_count += 1

    flush()

    write_text(root / "data" / "tracks.manifest.json", stable_json(manifest, pretty=True))


def rebuild_albums_and_indexes(root: Path, tracks: List[Dict[str, Any]], issues: List[ImportIssue]) -> None:
    albums_dir = root / "data" / "albums"
    indexes_dir = root / "indexes"

    if albums_dir.exists():
        shutil.rmtree(albums_dir)
    albums_dir.mkdir(parents=True, exist_ok=True)
    indexes_dir.mkdir(parents=True, exist_ok=True)

    by_album_key: Dict[Tuple[str, str, str], List[Dict[str, Any]]] = collections.defaultdict(list)
    by_id: Dict[str, List[Dict[str, Any]]] = collections.defaultdict(list)
    by_artist: Dict[str, List[str]] = collections.defaultdict(list)
    by_album: Dict[str, List[str]] = collections.defaultdict(list)
    by_track_title: Dict[str, List[Dict[str, Any]]] = collections.defaultdict(list)

    for t in tracks:
        artist = str(t.get("artist") or "Unknown Artist")
        album = str(t.get("album") or "Unknown Album")
        vid = str(t.get("id") or "")

        by_album_key[(artist, album, vid)].append(t)
        by_id[vid].append({"start": t.get("start"), "title": t.get("title"), "artist": artist, "album": album})
        by_artist[artist].append(album)
        by_album[album].append(artist)
        by_track_title[str(t.get("title") or "")].append({"id": vid, "start": t.get("start"), "artist": artist, "album": album})

    for (artist, album, vid), group in by_album_key.items():
        group.sort(key=lambda x: int(x.get("start") or 0))
        album_obj = {
            "id": vid,
            "artist": artist,
            "album": album,
            "album_artist": group[0].get("album_artist") or artist,
            "tracks": [
                {
                    "start": t.get("start"),
                    "end": t.get("end"),
                    "title": t.get("title"),
                    "url": t.get("url"),
                }
                for t in group
            ],
        }

        file_name = f"{safe_filename(artist)} - {safe_filename(album)} [{safe_filename(vid)}].json"
        write_text(albums_dir / file_name, stable_json(album_obj, pretty=True))

    by_artist_out = {k: sorted(set(v)) for k, v in sorted(by_artist.items())}
    by_album_out = {k: sorted(set(v)) for k, v in sorted(by_album.items())}

    write_text(indexes_dir / "by_id.json", stable_json(by_id, pretty=True))
    write_text(indexes_dir / "by_artist.json", stable_json(by_artist_out, pretty=True))
    write_text(indexes_dir / "by_album.json", stable_json(by_album_out, pretty=True))
    write_text(indexes_dir / "by_track_title.json", stable_json(by_track_title, pretty=True))

    catalog = {
        "total_tracks": len(tracks),
        "total_videos": len(by_id),
        "total_artists": len(by_artist_out),
        "total_albums": len(by_album_out),
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    write_text(indexes_dir / "catalog.json", stable_json(catalog, pretty=True))

    issues_obj = [dataclasses.asdict(i) for i in issues]
    write_text(indexes_dir / "issues.json", stable_json(issues_obj, pretty=True))


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def load_cookie(args: argparse.Namespace) -> str:
    if args.cookie:
        return args.cookie

    if args.cookie_file:
        path = Path(args.cookie_file)
        if path.exists():
            return read_text(path).strip()

    return ""


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Import comment timelines into tracker-songs Git database.")
    parser.add_argument("--root", default=".", help="repository root directory")
    parser.add_argument("--input", required=True, help="input text/json file containing video IDs and timelines")
    parser.add_argument("--cookie", default="", help="optional request cookie")
    parser.add_argument("--cookie-file", default="", help="optional file containing request cookie")
    parser.add_argument("--no-network", action="store_true", help="do not request online APIs")
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT, help="HTTP timeout seconds")
    parser.add_argument("--shard-size", type=int, default=DEFAULT_SHARD_SIZE, help="target max shard size in bytes")
    parser.add_argument("--dry-run", action="store_true", help="parse and enrich, but do not write database")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    input_path = Path(args.input).resolve()
    cookie = load_cookie(args)

    entries = load_import_entries(input_path)
    if not entries:
        print("No valid import entries found.", file=sys.stderr)
        return 2

    issues: List[ImportIssue] = []
    incoming: List[Dict[str, Any]] = []

    for entry in entries:
        print(f"Importing {entry.id} ...")
        new_tracks = build_tracks_for_entry(
            entry=entry,
            cookie=cookie,
            no_network=args.no_network,
            timeout=args.timeout,
            issues=issues,
        )
        print(f"  parsed tracks: {len(new_tracks)}")
        incoming.extend(new_tracks)

    if not incoming:
        print("No tracks imported.", file=sys.stderr)
        if issues:
            print(f"Issues: {len(issues)}", file=sys.stderr)
        return 3

    existing = load_existing_tracks(root)
    merged = merge_tracks(existing, incoming)

    print(f"Existing tracks: {len(existing)}")
    print(f"Incoming tracks: {len(incoming)}")
    print(f"Merged tracks:   {len(merged)}")
    print(f"Issues:          {len(issues)}")

    if args.dry_run:
        for issue in issues[:20]:
            print(f"[{issue.type}] {issue.id}: {issue.message} :: {issue.line}", file=sys.stderr)
        return 0

    rebuild_shards(root, merged, args.shard_size)
    rebuild_albums_and_indexes(root, merged, issues)

    print("Done.")
    print("Updated:")
    print("  data/tracks.manifest.json")
    print("  data/tracks/*.jsonl")
    print("  data/albums/*.json")
    print("  indexes/*.json")

    if issues:
        print("Some lines were skipped. See indexes/issues.json")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
