package de.blau.android;

import org.acra.ACRA;
import org.acra.ReportingInteractionMode;
import org.acra.annotation.ReportsCrashes;

import de.blau.android.osb.BugStorage;
import de.blau.android.osm.StorageDelegator;

@ReportsCrashes(
	formKey = "",
	reportType = org.acra.sender.HttpSender.Type.JSON,
	httpMethod = org.acra.sender.HttpSender.Method.PUT,
	formUri = "http://acralyzer.vespucci.io/acraproxy",
	mode = ReportingInteractionMode.NOTIFICATION,
	resNotifTickerText = R.string.crash_notif_ticker_text,
	resNotifTitle = R.string.crash_notif_title,
	resNotifText = R.string.crash_notif_text,
	resDialogText = R.string.crash_dialog_text)
public class Application extends android.app.Application {
	public static Main mainActivity;
	static StorageDelegator delegator = new StorageDelegator();
	static BugStorage bugStorage = new BugStorage();
	public static String userAgent;
	
	@Override
	public void onCreate() {
		// The following line triggers the initialization of ACRA
		ACRA.init(this);
		super.onCreate();
		String appName = getString(R.string.app_name);
		String appVersion = getString(R.string.app_version);
		userAgent = appName + "/" + appVersion;
	}

	public static StorageDelegator getDelegator() {
		return delegator;
	}
	
	public static BugStorage getBugStorage() {
		return bugStorage;
	}
}