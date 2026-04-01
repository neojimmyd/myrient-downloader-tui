"""Shared utility functions — name normalization, parsing helpers."""
from __future__ import annotations

import re

from .constants import DISC_REGEX as _DISC_RE

# ── Pre-compiled regexes for ROM name normalization ─────────────────────────
# Matches common ROM file extensions (archives + raw game files).
_EXT_RE = re.compile(
    r'\.(?:zip|7z|rvz|chd|iso|wux|wbfs|gcz|xiso|bin|cue|img|gdi|nrg|mdf|mds|rom|ecm)$',
    re.IGNORECASE,
)

# Matches parenthesized tags: (USA), (v1.1), (Disc 1), (Beta), (En,Fr), etc.
_PAREN_TAG_RE = re.compile(r'\s*\([^)]*\)')

# Matches bracketed tags: [BIOS], [b], [!], [h1], etc.
_BRACKET_TAG_RE = re.compile(r'\s*\[[^\]]*\]')

# Matches revision/version tags: (Rev 1), (Rev A), (v1.0), (v1.1), (v2.20), etc.
_REV_RE = re.compile(r'\(((?:Rev\s+\S+|v\d+\.\d+\S*))\)', re.IGNORECASE)

# Trailing junk after stripping tags: leftover hyphens, commas, whitespace.
_TRAILING_JUNK_RE = re.compile(r'[\s,\-]+$')


def extract_region(filename: str) -> str:
    """Extract the first parenthesized tag (typically the region) from a ROM filename.

    >>> extract_region("Final Fantasy VII (USA) (Disc 1).7z")
    'USA'
    >>> extract_region("Gran Turismo (Europe) (v1.1).zip")
    'Europe'
    >>> extract_region("Ico")
    ''
    """
    m = _PAREN_TAG_RE.search(filename)
    if m:
        return m.group(0).strip().strip('()')
    return ''


def extract_revision(filename: str) -> str:
    """Extract the revision/version tag from a ROM filename.

    >>> extract_revision("Gran Turismo 2 (USA) (Rev 1).zip")
    'Rev 1'
    >>> extract_revision("Game (Europe) (v1.1).zip")
    'v1.1'
    >>> extract_revision("Ico (USA).zip")
    ''
    """
    m = _REV_RE.search(filename)
    return m.group(1) if m else ''


def strip_extension(filename: str) -> str:
    """Remove only the ROM file extension, keeping all tags intact.

    >>> strip_extension("Final Fantasy VII (USA) (Disc 1).7z")
    'Final Fantasy VII (USA) (Disc 1)'
    >>> strip_extension("Ico (USA).zip")
    'Ico (USA)'
    """
    return _EXT_RE.sub('', filename)


def _normalize_core(filename: str, keep_disc: bool = False) -> str:
    """Shared logic for ROM title normalization.

    Strips extension, parenthesized/bracketed tags, and trailing junk.
    When *keep_disc* is True, disc/tape/side indicators are preserved.
    """
    name = _EXT_RE.sub('', filename)
    disc_suffix = ''
    if keep_disc:
        disc_match = _DISC_RE.search(name)
        disc_suffix = disc_match.group(0).strip() if disc_match else ''
    name = _PAREN_TAG_RE.sub('', name)
    # Preserve leading [BIOS] but strip other bracket tags
    bios_prefix = ''
    if name.startswith('[BIOS]'):
        bios_prefix = '[BIOS] '
        name = name[6:]
    name = _BRACKET_TAG_RE.sub('', name)
    name = _TRAILING_JUNK_RE.sub('', name).strip()
    if bios_prefix and name:
        name = bios_prefix + name
    if disc_suffix:
        name = f"{name} {disc_suffix}"
    return name or filename


def normalize_game_title(filename: str) -> str:
    """Strip extension and all parenthesized/bracketed tags to get a clean title.

    >>> normalize_game_title("Final Fantasy VII (USA) (Disc 1).7z")
    'Final Fantasy VII'
    >>> normalize_game_title("Gran Turismo 2 - Arcade Mode (USA) (v1.1).zip")
    'Gran Turismo 2 - Arcade Mode'
    >>> normalize_game_title("Ico (USA).zip")
    'Ico'
    >>> normalize_game_title("[BIOS] PlayStation 2 (Europe) (v2.20).zip")
    '[BIOS] PlayStation 2'
    """
    return _normalize_core(filename, keep_disc=False)


def normalize_game_title_keep_disc(filename: str) -> str:
    """Like normalize_game_title but preserves disc/tape/side indicators.

    >>> normalize_game_title_keep_disc("Final Fantasy VII (USA) (Disc 1).7z")
    'Final Fantasy VII (Disc 1)'
    >>> normalize_game_title_keep_disc("Ico (USA).zip")
    'Ico'
    """
    return _normalize_core(filename, keep_disc=True)
