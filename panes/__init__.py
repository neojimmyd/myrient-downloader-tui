"""Pane widget classes — purely for compose() organisation.

All event handling, state, and workers remain on MyrientTUI.
Messages bubble up through the DOM normally; query_one() searches all
descendants, so nothing changes for the handler layer.
"""

from panes.browse import BrowsePane, GameSearchInput
from panes.downloads import DownloadsPane
from panes.library import LibraryPane
from panes.settings import SettingsPane
from panes.logs import LogsPane

__all__ = [
    "BrowsePane",
    "DownloadsPane",
    "GameSearchInput",
    "LibraryPane",
    "SettingsPane",
    "LogsPane",
]
