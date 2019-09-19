package de.blau.android.layer.mapillary;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Serializable;
import java.net.URL;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.ReentrantLock;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.mapbox.geojson.CoordinateContainer;
import com.mapbox.geojson.Feature;
import com.mapbox.geojson.FeatureCollection;
import com.mapbox.geojson.Geometry;
import com.mapbox.geojson.Point;

import android.app.Activity;
import android.content.Context;
import android.content.Intent;
import android.graphics.Canvas;
import android.graphics.Paint;
import android.graphics.Path;
import android.net.Uri;
import android.os.AsyncTask;
import android.support.annotation.NonNull;
import android.support.annotation.Nullable;
import android.support.v4.app.FragmentActivity;
import android.util.Log;
import de.blau.android.App;
import de.blau.android.Map;
import de.blau.android.PostAsyncActionHandler;
import de.blau.android.R;
import de.blau.android.layer.ClickableInterface;
import de.blau.android.layer.DiscardInterface;
import de.blau.android.layer.ExtentInterface;
import de.blau.android.layer.MapViewLayer;
import de.blau.android.osm.BoundingBox;
import de.blau.android.osm.OsmXml;
import de.blau.android.osm.ViewBox;
import de.blau.android.resources.DataStyle;
import de.blau.android.util.GeoJSONConstants;
import de.blau.android.util.GeoJson;
import de.blau.android.util.GeoMath;
import de.blau.android.util.SavingHelper;
import de.blau.android.util.Snack;
import de.blau.android.util.collections.FloatPrimitiveList;
import de.blau.android.util.rtree.BoundedObject;
import de.blau.android.util.rtree.RTree;
import de.blau.android.views.IMapView;
import okhttp3.Call;
import okhttp3.OkHttpClient;
import okhttp3.Request;
import okhttp3.Response;
import okhttp3.ResponseBody;

public class MapOverlay extends MapViewLayer implements Serializable, ExtentInterface, DiscardInterface, ClickableInterface<String> {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private static final String DEBUG_TAG = MapOverlay.class.getName();

    /**
     * when reading state lockout writing/reading
     */
    private transient ReentrantLock readingLock = new ReentrantLock();

    public static final String FILENAME = "mapillary.res";

    private transient SavingHelper<MapOverlay> savingHelper = new SavingHelper<>();
    private transient boolean                  saved        = false;

    /**
     * Wrapper around mapboxes Feature class makes the object serializable and usable in an RTree
     * 
     * @author Simon Poole
     *
     */
    class MapillaryObject implements BoundedObject, Serializable {
        private static final long serialVersionUID = 1;

        Feature     feature = null;
        BoundingBox box     = null;

        /**
         * Constructor
         * 
         * @param f the Feature to wrap
         */
        public MapillaryObject(@NonNull Feature f) {
            this.feature = f;
        }

        @Override
        public BoundingBox getBounds() {
            if (box == null) {
                box = GeoJson.getBounds(feature.geometry());
            }
            return box;
        }

        /**
         * Get the wrapped Feature object
         * 
         * @return the Feature
         */
        @Nullable
        public Feature getFeature() {
            return feature;
        }

        /**
         * Serialize this object
         * 
         * @param out ObjectOutputStream to write to
         * @throws IOException
         */
        private void writeObject(java.io.ObjectOutputStream out) throws IOException {
            out.writeUTF(feature.toJson());
            out.writeObject(box);
        }

        /**
         * Recreate the object for serialized state
         * 
         * @param in ObjectInputStream to write from
         * @throws IOException
         * @throws ClassNotFoundException
         */
        private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
            String jsonString = in.readUTF();
            feature = Feature.fromJson(jsonString);
            box = (BoundingBox) in.readObject();
        }
    }

    private static final int SHOW_MARKER_ZOOM = 20;

    private RTree                        data;
    private RTree                        boxes;
    private transient Paint              paint;
    private final transient Path         path   = new Path();
    private transient FloatPrimitiveList points = new FloatPrimitiveList();

    /** Map this is an overlay of. */
    private final transient Map map;

    /**
     * Styling parameters
     */
    private int   iconRadius;
    private int   color;
    private float strokeWidth;

    /**
     * Name for this layer (typically the file name)
     */
    private String name;

    /**
     * Construct this layer
     * 
     * @param map the Map object we are displayed on
     */
    public MapOverlay(final Map map) {
        this.map = map;
        paint = new Paint(DataStyle.getInternal(DataStyle.GEOJSON_DEFAULT).getPaint());
    }

    @Override
    public boolean isReadyToDraw() {
        return data != null;
    }

    @Override
    protected void onDraw(Canvas canvas, IMapView osmv) {
        if (!isVisible || data == null) {
            return;
        }
        ViewBox bb = osmv.getViewBox();
        int width = map.getWidth();
        int height = map.getHeight();
        int zoomLevel = map.getZoomLevel();

        Collection<BoundedObject> queryResult = new ArrayList<>();
        data.query(queryResult, bb);
        Log.d(DEBUG_TAG, "features result count " + queryResult.size());
        for (BoundedObject bo : queryResult) {
            Feature f = ((MapillaryObject) bo).getFeature();
            drawSequence(canvas, bb, width, height, f, paint, zoomLevel >= SHOW_MARKER_ZOOM);
        }
    }

    /**
     * Draw a line for a sequence with optional markers for the images
     * 
     * @param canvas Canvas object we are drawing on
     * @param bb the current ViewBox
     * @param width screen width in screen coordinates
     * @param height screen height in screen coordinates
     * @param f the GeoJson Feature holding the sequence
     * @param paint Paint object for drawing
     * @param withMarker if true show the markers
     */
    public void drawSequence(@NonNull Canvas canvas, @NonNull ViewBox bb, int width, int height, @NonNull Feature f, @NonNull Paint paint, boolean withMarker) {
        paint.setAntiAlias(true);
        paint.setStyle(Paint.Style.STROKE);
        path.reset();
        @SuppressWarnings("unchecked")
        List<Point> line = ((CoordinateContainer<List<Point>>) f.geometry()).coordinates();
        JsonObject coordinateProperties = (JsonObject) f.getProperty("coordinateProperties");
        JsonArray cas = coordinateProperties.get("cas").getAsJsonArray();
        int size = line.size();
        Path mapillaryPath = DataStyle.getCurrent().getMapillaryPath();
        GeoJson.pointListToLinePointsArray(bb, width, height, points, line);
        float[] linePoints = points.getArray();
        int pointsSize = points.size();
        if (pointsSize > 2) {
            path.reset();
            path.moveTo(linePoints[0], linePoints[1]);
            for (int i = 0; i < pointsSize; i = i + 4) {
                path.lineTo(linePoints[i + 2], linePoints[i + 3]);
            }
            canvas.drawPath(path, paint);
        }
        if (withMarker) {
            for (int i = 0; i < size; i++) {
                Point p = line.get(i);
                double longitude = p.longitude();
                double latitude = p.latitude();
                if (bb.contains(longitude, latitude)) {
                    float x = GeoMath.lonToX(width, bb, longitude);
                    float y = GeoMath.latToY(height, width, bb, latitude);
                    drawMarker(canvas, x, y, cas.get(i).getAsInt(), paint, mapillaryPath);
                }
            }
        }
    }

    /**
     * Show a marker for the current GPS position
     * 
     * @param canvas canvas to draw on
     * @param x screen x
     * @param y screen y
     * @param o cardinal orientation in degrees
     * @param paint Paint object to use
     * @param path Path for the marker
     */
    private void drawMarker(@NonNull final Canvas canvas, float x, float y, float o, Paint paint, Path path) {
        if (o < 0) {
            // no orientation data available
            canvas.drawCircle(x, y, paint.getStrokeWidth(), paint);
        } else {
            // show the orientation using a pointy indicator
            canvas.save();
            canvas.translate(x, y);
            canvas.rotate(o);
            canvas.drawPath(path, paint);
            canvas.restore();
        }
    }

    @Override
    protected void onDrawFinished(Canvas c, IMapView osmv) {
        // do nothing
    }

    @Override
    public void onDestroy() {
        data = null;
    }

    /**
     * @param features a List of Feature
     */
    private void loadFeatures(List<Feature> features) {
        for (Feature f : features) {
            if (GeoJSONConstants.FEATURE.equals(f.type()) && f.geometry() != null) {
                data.insert(new MapillaryObject(f));
            } else {
                Log.e(DEBUG_TAG, "Type of object " + f.type() + " geometry " + f.geometry());
            }
        }
    }

    /**
     * Stores the current state to the default storage file
     * 
     * @param context Android Context
     * @throws IOException on errors writing the file
     */
    public synchronized void onSaveState(@NonNull Context context) throws IOException {
        super.onSaveState(context);
        if (saved) {
            Log.i(DEBUG_TAG, "state not dirty, skipping save");
            return;
        }
        if (readingLock.tryLock()) {
            try {
                // TODO this doesn't really help with error conditions need to throw exception
                if (savingHelper.save(context, FILENAME, this, true)) {
                    saved = true;
                } else {
                    // this is essentially catastrophic and can only happen if something went really wrong
                    // running out of memory or disk, or HW failure
                    if (context instanceof Activity) {
                        Snack.barError((Activity) context, R.string.toast_statesave_failed);
                    }
                }
            } finally {
                readingLock.unlock();
            }
        } else {
            Log.i(DEBUG_TAG, "bug state being read, skipping save");
        }
    }

    /**
     * Loads any saved state from the default storage file
     * 
     * 
     * @param context Android context
     * @return true if the saved state was successfully read
     */
    public synchronized boolean onRestoreState(@NonNull Context context) {
        super.onRestoreState(context);
        try {
            readingLock.lock();
            if (data != null && data.count() > 0) {
                // don't restore over existing data
                return true;
            }
            // disable drawing
            setVisible(false);
            MapOverlay restoredOverlay = savingHelper.load(context, FILENAME, true);
            if (restoredOverlay != null) {
                Log.d(DEBUG_TAG, "read saved state");
                data = restoredOverlay.data;
                iconRadius = restoredOverlay.iconRadius;
                color = restoredOverlay.color;
                // paint.setColor(color);
                strokeWidth = restoredOverlay.strokeWidth;
                // paint.setStrokeWidth(strokeWidth);
                name = restoredOverlay.name;
                return true;
            } else {
                Log.d(DEBUG_TAG, "saved state null");
                return false;
            }
        } finally {
            // re-enable drawing
            setVisible(true);
            readingLock.unlock();
        }
    }

    /**
     * Given screen coordinates, find all nearby elements.
     *
     * @param x Screen X-coordinate.
     * @param y Screen Y-coordinate.
     * @param viewBox Map view box.
     * @return List of photos close to given location.
     */
    @Override
    public List<String> getClicked(final float x, final float y, final ViewBox viewBox) {
        List<String> result = new ArrayList<>();
        Log.d(DEBUG_TAG, "getClicked");
        if (data != null) {
            final float tolerance = DataStyle.getCurrent().getNodeToleranceValue();
            Collection<BoundedObject> queryResult = new ArrayList<>();
            data.query(queryResult, viewBox);
            Log.d(DEBUG_TAG, "features result count " + queryResult.size());
            if (queryResult != null) {
                for (BoundedObject bo : queryResult) {
                    Feature f = ((MapillaryObject) bo).getFeature();
                    Geometry g = f.geometry();
                    if (g == null) {
                        continue;
                    }
                    switch (g.type()) {
                    case GeoJSONConstants.LINESTRING:
                        @SuppressWarnings("unchecked")
                        List<Point> line = ((CoordinateContainer<List<Point>>) f.geometry()).coordinates();
                        JsonObject coordinateProperties = (JsonObject) f.getProperty("coordinateProperties");
                        JsonArray imageKeys = coordinateProperties.get("image_keys").getAsJsonArray();
                        for (int i = 0; i < line.size(); i++) {
                            if (inToleranceArea(viewBox, tolerance, line.get(i), x, y)) {
                                result.add(imageKeys.get(i).getAsString());
                            }
                        }
                        break;

                    default:
                    }
                }
            }
        }
        Log.d(DEBUG_TAG, "getClicked found " + result.size());
        return result;
    }

    /**
     * Check if the current touch position is in the tolerance area around a Position
     * 
     * @param viewBox the current screen ViewBox
     * @param tolerance the tolerance value
     * @param p the Position
     * @param x screen x coordinate of touch location
     * @param y screen y coordinate of touch location
     * @return true if touch position is in tolerance
     */
    private boolean inToleranceArea(@NonNull ViewBox viewBox, float tolerance, @NonNull Point p, float x, float y) {
        float differenceX = Math.abs(GeoMath.lonToX(map.getWidth(), viewBox, p.longitude()) - x);
        float differenceY = Math.abs(GeoMath.latToY(map.getHeight(), map.getWidth(), viewBox, p.latitude()) - y);
        return differenceX <= tolerance && differenceY <= tolerance && Math.hypot(differenceX, differenceY) <= tolerance;
    }

    /**
     * Return a List of all loaded Features
     * 
     * @return a List of Feature objects
     */
    public List<Feature> getFeatures() {
        Collection<BoundedObject> queryResult = new ArrayList<>();
        data.query(queryResult);
        List<Feature> result = new ArrayList<>();
        for (BoundedObject bo : queryResult) {
            result.add(((MapillaryObject) bo).getFeature());
        }
        return result;
    }

    @Override
    public String getName() {

        return "Mapillary"; // map.getContext().getString(R.string.layer_geojson);
    }

    @Override
    public void invalidate() {
        map.invalidate();
    }

    @Override
    public BoundingBox getExtent() {
        if (data != null) {
            Collection<BoundedObject> queryResult = new ArrayList<>();
            data.query(queryResult);
            BoundingBox extent = null;
            for (BoundedObject bo : queryResult) {
                if (extent == null) {
                    extent = bo.getBounds();
                } else {
                    extent.union(bo.getBounds());
                }
            }
            return extent;
        }
        return null;
    }

    @Override
    public boolean isEnabled() {
        return data != null && data.count() > 0;
    }

    @Override
    public void discard(Context context) {
        if (readingLock.tryLock()) {
            try {
                data = null;
                File originalFile = context.getFileStreamPath(FILENAME);
                if (!originalFile.delete()) {
                    Log.e(DEBUG_TAG, "Failed to delete state file " + FILENAME);
                }
            } finally {
                readingLock.unlock();
            }
        }
        map.invalidate();
    }

    @Override
    public void onSelected(FragmentActivity activity, String imageKey) {
        Uri uri = Uri.parse("https://images.mapillary.com/" + imageKey + "/thumb-2048.jpg");
        activity.startActivity(new Intent(Intent.ACTION_VIEW, uri));
    }

    @Override
    public String getDescription(String s) {

        return s;
    }

    @Override
    public String getSelected() {
        return null;
    }

    @Override
    public void deselectObjects() {
        // not used
    }

    @Override
    public void setSelected(String o) {
        // not used
    }

    /**
     * Download tasks for a bounding box, actual requests will depend on what the current filter for tasks is set to
     * 
     * @param context Android context
     * @param box the bounding box
     * @param handler handler to run after the download if not null
     */
    public void downloadBox(@NonNull final Context context, @NonNull final BoundingBox box, @Nullable final PostAsyncActionHandler handler) {

        if (data == null) {
            data = new RTree(2, 12);
        }
        box.makeValidForApi();

        new AsyncTask<Void, Void, Void>() {
            @Override
            protected Void doInBackground(Void... params) {
                Log.d(DEBUG_TAG, "querying server for " + box);
                try {
                    Log.d(DEBUG_TAG, "getBugssForBox");
                    URL url;

                    url = new URL("https://a.mapillary.com/v3/sequences?client_id=OUFiX0ZWQmtTeUhCc3UycG96eXViZzo2MmRmYTRlZmM3ZTY3Nzhh" + "&bbox="
                            + box.getLeft() / 1E7d + "," + box.getBottom() / 1E7d + "," + box.getRight() / 1E7d + "," + box.getTop() / 1E7d);
                    Log.d(DEBUG_TAG, "query: " + url.toString());
                    ResponseBody responseBody = null;
                    InputStream inputStream = null;

                    Request request = new Request.Builder().url(url).build();
                    OkHttpClient client = App.getHttpClient().newBuilder().connectTimeout(20000, TimeUnit.MILLISECONDS)
                            .readTimeout(20000, TimeUnit.MILLISECONDS).build();
                    Call mapillaryCall = client.newCall(request);
                    Response mapillaryCallResponse = mapillaryCall.execute();
                    if (mapillaryCallResponse.isSuccessful()) {
                        responseBody = mapillaryCallResponse.body();
                        inputStream = responseBody.byteStream();
                    } else {

                    }

                    BufferedReader rd = new BufferedReader(new InputStreamReader(inputStream, Charset.forName(OsmXml.UTF_8)));
                    StringBuilder sb = new StringBuilder();
                    int cp;
                    while ((cp = rd.read()) != -1) {
                        sb.append((char) cp);
                    }
                    try {
                        FeatureCollection fc = FeatureCollection.fromJson(sb.toString());
                        for (Feature f : fc.features()) {
                            data.insert(new MapillaryObject(f));
                        }
                    } catch (Exception e) {
                        Log.e(DEBUG_TAG, "Fatal error parsing " + url + " " + e.getMessage());
                    }
                } catch (Exception ex) {
                }
                return null;
            }

            @Override
            protected void onPostExecute(Void param) {
                if (handler != null) {
                    handler.onSuccess();
                }
            }
        }.execute();
    }

}
