package de.blau.android.layer.mapillary;

import java.util.Date;

class MapillaryImage {
    String key;
    String username;
    long   capturedAt;
    int    index;

    @Override
    public String toString() {
        return username + " " + (new Date(capturedAt)).toLocaleString() + " " + index;
    }
}
