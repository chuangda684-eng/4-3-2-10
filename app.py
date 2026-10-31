"""WanTrip: 候補地の天気と、周辺の施設検索。

天気は Open-Meteo。施設は Google Places API (New) の Nearby Search。
天気に APIキーは不要。施設検索と地図は、環境変数か Streamlit の secrets から別々のキーを読む。
"""

import hashlib
import json
import math
import os
import re
import secrets
from datetime import date
from pathlib import Path
from urllib.parse import quote, urlencode, urlparse

import requests
import streamlit as st

# 予報APIのアドレス。地名ではなく、緯度と経度を渡して天気を受け取る。
OPEN_METEO_FORECAST_URL = "https://api.open-meteo.com/v1/forecast"
PLACES_SEARCH_URL = "https://places.googleapis.com/v1/places:searchNearby"
# 名前・住所・座標・Place ID・地図URL・種別だけを受け取る。レビューや写真は取らない。
PLACES_FIELD_MASK = (
    "places.id,places.displayName,places.formattedAddress,places.location,"
    "places.googleMapsUri,places.primaryType,places.types,places.attributions"
)
APP_DIR = Path(__file__).resolve().parent
STATIC_DIR = APP_DIR / "static"
MAP_FILE_PREFIX = "wantrip-map"
# セッションIDは secrets.token_hex(16)、検索トークンは内容ハッシュの先頭16桁。
_SESSION_ID_RE = re.compile(r"^[0-9a-f]{32}$")
_SEARCH_TOKEN_RE = re.compile(r"^[0-9a-f]{16}$")
_MAP_FILE_RE = re.compile(r"^wantrip-map-[0-9a-f]{32}-[0-9a-f]{16}\.html$")
REQUEST_TIMEOUT_SECONDS = 10
PLACES_TIMEOUT_SECONDS = 15
SEARCH_RADIUS_METERS = 10_000
# Nearby Search (New) が1回で返せる上限。
MAX_RESULT_COUNT = 20
WEEKDAYS = "月火水木金土日"
# 犬同伴の内部値。画面の文言は DOG_STATUS_LABELS だけを使う。
DOG_STATUS_ALLOWED = "allowed"
DOG_STATUS_NOT_ALLOWED = "not_allowed"
DOG_STATUS_UNKNOWN_VALUE = "unknown"
DOG_STATUS_LABELS = {
    DOG_STATUS_ALLOWED: "犬同伴OK",
    DOG_STATUS_NOT_ALLOWED: "犬同伴不可",
    DOG_STATUS_UNKNOWN_VALUE: "未確認",
}
# InfoWindow は親の薄い文字色を受け継ぐため、ステータスごとに色を直接指定する。
DOG_STATUS_COLORS = {
    DOG_STATUS_ALLOWED: "#137333",
    DOG_STATUS_NOT_ALLOWED: "#C5221F",
    DOG_STATUS_UNKNOWN_VALUE: "#444444",
}
DOG_FILTER_ALL = "すべて"
DOG_FILTER_ALLOWED_ONLY = "同伴OKのみ"
DOG_FILTER_INCLUDE_UNKNOWN = "未確認を含む"
DOG_FILTER_EXCLUDE_DENIED = "同伴不可を除外"
DOG_FILTERS = (
    DOG_FILTER_ALL,
    DOG_FILTER_ALLOWED_ONLY,
    DOG_FILTER_INCLUDE_UNKNOWN,
    DOG_FILTER_EXCLUDE_DENIED,
)
# 公式情報で確認できた施設だけを place_id で書く。名前やカテゴリーでは判定しない。
# ここに無い施設は unknown。値の例:
# "place_id": {
#     "dog_friendly_status": "allowed",
#     "dog_friendly_source": "施設の公式サイト",
#     "dog_friendly_note": "リード着用。小型犬のみ。",
#     "dog_friendly_checked_at": "2026-10-31",
# }
DOG_FRIENDLY_CONFIRMATIONS = {}

# 目的地の代表点（緯度, 経度）。天気も施設検索も、この座標を中心にする。
LOCATIONS = {
    "飯田市": (35.51965, 137.82074),
    "東京": (35.6895, 139.69171),
    "大阪": (34.69379, 135.50107),
    "横浜": (35.43333, 139.65),
    "名古屋": (35.18147, 136.9064),
    "札幌": (43.06667, 141.35),
    "福岡": (33.6, 130.41667),
    "京都": (35.02107, 135.75385),
}

DOG_SIZES = [
    "小型犬（おおむね10kg未満）",
    "中型犬（おおむね10〜25kg）",
    "大型犬（おおむね25kg以上）",
]

FACILITY_TYPES = [
    "ドッグラン",
    "犬同伴可能なカフェ",
    "公園",
    "犬同伴可能な宿泊施設",
    "ペットショップ",
]

# Google Places の Table A にある種別だけを使う。カテゴリーごとに種類を変える。
CATEGORY_TYPES = {
    "ドッグラン": ("dog_park",),
    "犬同伴可能なカフェ": ("cafe",),
    "公園": ("park",),
    "犬同伴可能な宿泊施設": ("lodging", "hotel", "motel", "hostel", "guest_house"),
    "ペットショップ": ("pet_store",),
}
# 1件が複数の種別に当たるときは、上から先にカテゴリーを決める。
TYPE_CATEGORY = (
    ("dog_park", "ドッグラン"),
    ("pet_store", "ペットショップ"),
    ("cafe", "犬同伴可能なカフェ"),
    ("lodging", "犬同伴可能な宿泊施設"),
    ("hotel", "犬同伴可能な宿泊施設"),
    ("motel", "犬同伴可能な宿泊施設"),
    ("hostel", "犬同伴可能な宿泊施設"),
    ("guest_house", "犬同伴可能な宿泊施設"),
    ("park", "公園"),
)
MARKER_COLORS = {
    "ドッグラン": "#E53935",
    "犬同伴可能なカフェ": "#FB8C00",
    "公園": "#43A047",
    "犬同伴可能な宿泊施設": "#1E88E5",
    "ペットショップ": "#8E24AA",
}

# Open-Meteoの天気コードを、表示名と絵文字にする。
# 絵文字は「晴れ・曇り・雨・雪・雷雨・霧」の6種類。
WEATHER_CODE_MAP = {
    0: ("快晴", "☀️"),
    1: ("おおむね晴れ", "☀️"),
    2: ("一部曇り", "☁️"),
    3: ("曇り", "☁️"),
    45: ("霧", "🌫️"),
    48: ("霧", "🌫️"),
    51: ("霧雨", "🌧️"),
    53: ("霧雨", "🌧️"),
    55: ("霧雨", "🌧️"),
    61: ("雨", "🌧️"),
    63: ("雨", "🌧️"),
    65: ("雨", "🌧️"),
    66: ("凍るような雨", "🌧️"),
    67: ("凍るような雨", "🌧️"),
    71: ("雪", "❄️"),
    73: ("雪", "❄️"),
    75: ("雪", "❄️"),
    77: ("雪", "❄️"),
    80: ("にわか雨", "🌧️"),
    81: ("にわか雨", "🌧️"),
    82: ("にわか雨", "🌧️"),
    85: ("にわか雪", "❄️"),
    86: ("にわか雪", "❄️"),
    95: ("雷雨", "⛈️"),
    96: ("雷雨", "⛈️"),
    97: ("雷雨", "⛈️"),
    99: ("雷雨", "⛈️"),
}
UNKNOWN_WEATHER = ("天気不明", "❓")


def describe_weather(code):
    """天気コードを (表示名, 絵文字) にする。未定義のコードは天気不明。"""
    try:
        number = float(code)
    except (TypeError, ValueError):
        return UNKNOWN_WEATHER
    if not number.is_integer():
        return UNKNOWN_WEATHER
    return WEATHER_CODE_MAP.get(int(number), UNKNOWN_WEATHER)


def fetch_three_day_forecast(latitude, longitude):
    """今後3日間の天気、最高気温、降水確率を取得する。

    成功時は (日別のリスト, None)、失敗時は (None, 画面に出すメッセージ)。
    weather_code が無くても、気温と降水確率が取れれば成功にする。
    """
    params = {
        "latitude": latitude,
        "longitude": longitude,
        "daily": "temperature_2m_max,precipitation_probability_max,weather_code",
        "timezone": "Asia/Tokyo",
        "forecast_days": 3,
    }

    try:
        response = requests.get(
            OPEN_METEO_FORECAST_URL,
            params=params,
            timeout=REQUEST_TIMEOUT_SECONDS,
        )
        response.raise_for_status()
    except requests.Timeout:
        return None, "天気サーバーからの応答が時間内に返りませんでした。しばらくしてからもう一度試してください。"
    except requests.ConnectionError:
        return None, "天気サーバーに接続できませんでした。ネットワーク接続を確認してください。"
    except requests.HTTPError:
        return None, "天気サーバーがエラーを返しました。時間をおいてもう一度試してください。"
    except requests.RequestException:
        return None, "天気情報の取得に失敗しました。時間をおいてもう一度試してください。"

    try:
        data = response.json()
    except ValueError:
        return None, "天気サーバーの応答を読み取れませんでした。"

    daily = data.get("daily") if isinstance(data, dict) else None
    if not isinstance(daily, dict):
        return None, "天気データが見つかりませんでした。"

    # JSONの中の daily から、同じ順で並んだ配列を取り出す。
    dates = daily.get("time")
    temps = daily.get("temperature_2m_max")
    probs = daily.get("precipitation_probability_max")
    if not (
        isinstance(dates, list)
        and isinstance(temps, list)
        and isinstance(probs, list)
        and dates
        and len(dates) == len(temps) == len(probs)
    ):
        return None, "天気データの形式が想定と違ったため、表示できませんでした。"

    # 天気コードが欠けていても、日付ごとの表示は続ける。
    codes = daily.get("weather_code")
    if not isinstance(codes, list) or len(codes) != len(dates):
        codes = [None] * len(dates)

    rows = []
    for day, temp, prob, code in zip(dates, temps, probs, codes):
        try:
            date.fromisoformat(day)
            temp_value = float(temp)
            prob_value = float(prob)
        except (TypeError, ValueError):
            return None, "天気データの値を読み取れなかったため、表示できませんでした。"
        label, emoji = describe_weather(code)
        rows.append(
            {
                "date": day,
                "temp_max": temp_value,
                "precip_prob": prob_value,
                "weather_code": code,
                "label": label,
                "emoji": emoji,
            }
        )
    return rows, None


def format_forecast_date(iso_date):
    """'2026-10-29' を '2026年10月29日（木）' にする。"""
    parsed = date.fromisoformat(iso_date)
    weekday = WEEKDAYS[parsed.weekday()]
    return f"{parsed.year}年{parsed.month}月{parsed.day}日（{weekday}）"


class PlacesServiceError(Exception):
    """画面にそのまま出す、施設検索の失敗。"""


def _secret_or_env(name):
    """環境変数を優先し、無ければ st.secrets の同じ名前を見る。無ければ空文字。"""
    env_key = os.environ.get(name, "")
    if isinstance(env_key, str) and env_key.strip():
        return env_key.strip()
    try:
        secret = st.secrets[name]
    except Exception:
        return ""
    if not isinstance(secret, str):
        return ""
    return secret.strip()


def places_api_key():
    """Places API (New) 用。GOOGLE_PLACES_API_KEY。"""
    return _secret_or_env("GOOGLE_PLACES_API_KEY")


def maps_api_key():
    """地図の JavaScript API 用。GOOGLE_MAPS_API_KEY。ブラウザの地図だけに渡す。"""
    return _secret_or_env("GOOGLE_MAPS_API_KEY")


def selected_categories(categories):
    """選択順ではなく、画面の並びで安定したタプルにする。"""
    chosen = set(categories)
    return tuple(name for name in FACILITY_TYPES if name in chosen)


def included_types(categories):
    """選んだカテゴリーに対応する Google の施設種別。"""
    names = []
    for category in selected_categories(categories):
        for type_name in CATEGORY_TYPES[category]:
            if type_name not in names:
                names.append(type_name)
    return tuple(names)


def search_identity(place_name, categories):
    """地点・カテゴリー・半径・種別が違えば、別の検索として扱う。"""
    latitude, longitude = LOCATIONS[place_name]
    return (
        place_name,
        selected_categories(categories),
        round(float(latitude), 5),
        round(float(longitude), 5),
        SEARCH_RADIUS_METERS,
        included_types(categories),
    )


def _finite_coordinate(value, low, high):
    try:
        number = float(value)
    except (TypeError, ValueError):
        return None
    if not math.isfinite(number) or not (low <= number <= high):
        return None
    return number


def category_for_place(types, primary_type, allowed):
    """応答の種別から、選んだカテゴリーのどれかを1つ決める。"""
    type_set = set()
    if isinstance(types, list):
        type_set.update(str(item) for item in types if item)
    if primary_type:
        type_set.add(str(primary_type))
    for type_name, category in TYPE_CATEGORY:
        if type_name in type_set and category in allowed:
            return category
    return None


def normalize_place_id(raw_id):
    """Places API の id を Place ID だけにする。資源名の places/ は外す。"""
    text = str(raw_id or "").strip()
    if text.startswith("places/"):
        text = text[len("places/") :].strip()
    return text


def _google_maps_https(uri):
    """応答の googleMapsUri が Google の https URL か確かめる。"""
    parsed = urlparse(uri)
    if parsed.scheme != "https" or not parsed.netloc:
        return False
    host = parsed.netloc.lower().split(":")[0]
    if host.startswith("www."):
        host = host[4:]
    return host == "google.com" or host.endswith(".google.com") or host == "maps.app.goo.gl"


def google_maps_url(place_id, google_maps_uri):
    """この施設自身の URL だけを返す。施設名や座標からは作らない。"""
    uri = str(google_maps_uri or "").strip()
    if _google_maps_https(uri):
        return uri
    if not place_id:
        return ""
    # Maps URLs では query が必須。query_place_id でこの Place ID を開く。
    return "https://www.google.com/maps/search/?api=1&" + urlencode(
        {"query": f"place_id:{place_id}", "query_place_id": place_id}
    )


def normalize_dog_status(value):
    """内部値へ揃える。不明な値や、以前の画面文言「未確認」は unknown。"""
    if value in (DOG_STATUS_ALLOWED, DOG_STATUS_NOT_ALLOWED, DOG_STATUS_UNKNOWN_VALUE):
        return value
    if value == "未確認":
        return DOG_STATUS_UNKNOWN_VALUE
    return DOG_STATUS_UNKNOWN_VALUE


def dog_friendly_fields(place_id):
    """確認済みの公式情報だけを返す。登録が無い施設は未確認。"""
    raw = DOG_FRIENDLY_CONFIRMATIONS.get(place_id)
    if not isinstance(raw, dict):
        raw = {}
    source = str(raw.get("dog_friendly_source") or "").strip()
    status = normalize_dog_status(raw.get("dog_friendly_status"))
    # 確認元が無い判定は、公式情報がないものとして未確認に戻す。
    if status != DOG_STATUS_UNKNOWN_VALUE and not source:
        status = DOG_STATUS_UNKNOWN_VALUE
    return {
        "dog_friendly_status": status,
        "dog_friendly_source": source,
        "dog_friendly_note": str(raw.get("dog_friendly_note") or "").strip(),
        "dog_friendly_checked_at": str(raw.get("dog_friendly_checked_at") or "").strip(),
    }


def dog_status_view(place):
    """一覧と地図が同じ文言・補足を出すための表示用データ。"""
    if not isinstance(place, dict):
        place = {}
    status = normalize_dog_status(place.get("dog_friendly_status"))
    details = []
    note = str(place.get("dog_friendly_note") or "").strip()
    source = str(place.get("dog_friendly_source") or "").strip()
    checked_at = str(place.get("dog_friendly_checked_at") or "").strip()
    if note:
        details.append(note)
    if source:
        details.append(f"確認元: {source}")
    if checked_at:
        details.append(f"確認日: {checked_at}")
    return {
        "status": status,
        "label": DOG_STATUS_LABELS[status],
        "color": DOG_STATUS_COLORS[status],
        "details": details,
    }


def filter_places_by_dog_status(places, choice):
    """絞り込み後の施設。一覧と地図の両方に、この結果だけを渡す。

    「未確認を含む」は同伴OKと未確認。「同伴不可を除外」は同伴不可以外。
    公式の確認情報がまだ無いときは、どちらも未確認の施設が残る。
    """
    if choice == DOG_FILTER_ALLOWED_ONLY:
        visible = {DOG_STATUS_ALLOWED}
    elif choice in (DOG_FILTER_INCLUDE_UNKNOWN, DOG_FILTER_EXCLUDE_DENIED):
        visible = {DOG_STATUS_ALLOWED, DOG_STATUS_UNKNOWN_VALUE}
    else:
        visible = {
            DOG_STATUS_ALLOWED,
            DOG_STATUS_NOT_ALLOWED,
            DOG_STATUS_UNKNOWN_VALUE,
        }
    return [
        place
        for place in places
        if isinstance(place, dict)
        and normalize_dog_status(place.get("dog_friendly_status")) in visible
    ]


def place_from_api(raw, allowed_categories):
    """Places API の1件を、一覧とマーカーが共有する辞書にする。"""
    if not isinstance(raw, dict):
        return None
    place_id = normalize_place_id(raw.get("id"))
    if not place_id:
        return None
    display = raw.get("displayName")
    if isinstance(display, dict):
        name = str(display.get("text") or "").strip()
    else:
        name = str(display or "").strip()
    name = name or "名称不明"
    address = str(raw.get("formattedAddress") or "").strip()
    location = raw.get("location") if isinstance(raw.get("location"), dict) else {}
    latitude = _finite_coordinate(location.get("latitude"), -90, 90)
    longitude = _finite_coordinate(location.get("longitude"), -180, 180)
    category = category_for_place(
        raw.get("types"),
        raw.get("primaryType"),
        allowed_categories,
    )
    if category is None:
        return None
    return {
        "place_id": place_id,
        "name": name,
        "address": address,
        "latitude": latitude,
        "longitude": longitude,
        "category": category,
        "google_maps_url": google_maps_url(place_id, raw.get("googleMapsUri")),
        "marker_color": MARKER_COLORS[category],
        **dog_friendly_fields(place_id),
    }


def _attribution_texts(raw_places):
    texts = []
    for raw in raw_places:
        if not isinstance(raw, dict):
            continue
        attributions = raw.get("attributions")
        if not isinstance(attributions, list):
            continue
        for item in attributions:
            if isinstance(item, dict):
                provider = str(item.get("provider") or "").strip()
            else:
                provider = str(item or "").strip()
            if provider and provider not in texts:
                texts.append(provider)
    return texts


def places_from_response(data, categories):
    """応答全体を施設のリストにする。場所が無い応答は空のリスト。"""
    if not isinstance(data, dict):
        raise PlacesServiceError("施設の検索結果を読み取れませんでした。")
    if "error" in data and "places" not in data:
        raise PlacesServiceError("施設の検索結果を読み取れませんでした。")
    raw_places = data.get("places", [])
    if not isinstance(raw_places, list):
        raise PlacesServiceError("施設の検索結果を読み取れませんでした。")
    allowed = set(selected_categories(categories))
    places = []
    seen = set()
    for raw in raw_places:
        place = place_from_api(raw, allowed)
        if place is None or place["place_id"] in seen:
            continue
        seen.add(place["place_id"])
        places.append(place)
    order = {name: index for index, name in enumerate(FACILITY_TYPES)}
    places.sort(
        key=lambda place: (
            order.get(place["category"], 99),
            place["name"] == "名称不明",
            place["name"],
            place["place_id"],
        )
    )
    return places, _attribution_texts(raw_places)


def marker_records(places):
    """緯度・経度がある施設だけ、同じ辞書の値でマーカー用の記録を作る。"""
    records = []
    for place in places:
        if not isinstance(place, dict):
            continue
        latitude = place.get("latitude")
        longitude = place.get("longitude")
        if latitude is None or longitude is None:
            continue
        records.append(
            {
                "place_id": place.get("place_id", ""),
                "name": place.get("name") or "名称不明",
                "address": place.get("address") or "",
                "category": place.get("category") or "",
                "latitude": latitude,
                "longitude": longitude,
                "google_maps_url": place.get("google_maps_url") or "",
                "marker_color": place.get("marker_color") or "#E53935",
                "dog_friendly_status": place.get("dog_friendly_status"),
                "dog_friendly_source": place.get("dog_friendly_source") or "",
                "dog_friendly_note": place.get("dog_friendly_note") or "",
                "dog_friendly_checked_at": place.get("dog_friendly_checked_at") or "",
            }
        )
    return records


def build_places_map_html(places, maps_api_key):
    """同じ施設データから GoogleマップのHTMLを作る。座標が無ければ None。

    ここに渡すのは GOOGLE_MAPS_API_KEY だけ。Places 用キーは入れない。
    """
    records = marker_records(places)
    if not records or not maps_api_key:
        return None
    payload = []
    for record in records:
        dog_view = dog_status_view(record)
        payload.append(
            {
                "placeId": record["place_id"],
                "name": record["name"],
                "address": record["address"] or "住所は登録なし",
                "category": record["category"],
                "lat": record["latitude"],
                "lng": record["longitude"],
                "color": record["marker_color"],
                "url": record["google_maps_url"],
                "dogStatus": dog_view["label"],
                "dogStatusColor": dog_view["color"],
                "dogDetails": dog_view["details"],
            }
        )
    data_json = json.dumps(payload, ensure_ascii=False).replace("<", "\\u003c")
    center_lat = sum(item["lat"] for item in payload) / len(payload)
    center_lng = sum(item["lng"] for item in payload) / len(payload)
    zoom = 15 if len(payload) == 1 else 12
    script_src = (
        "https://maps.googleapis.com/maps/api/js?key="
        + quote(maps_api_key, safe="")
        + "&language=ja&region=JP"
    )
    return f"""<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <style>
    html, body {{ height: 100%; margin: 0; }}
    #map {{ height: 100%; min-height: 400px; color: #f5f5f5; background: #1e1e1e; }}
  </style>
</head>
<body>
  <div id="map"></div>
  <script id="wantrip-places" type="application/json">{data_json}</script>
  <script>
    const places = JSON.parse(document.getElementById("wantrip-places").textContent);
    function escapeHtml(value) {{
      return String(value)
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;");
    }}
    function wantripMapError() {{
      const mapElement = document.getElementById("map");
      mapElement.textContent = "地図を表示できませんでした。下の一覧からGoogleマップを開いてください。";
    }}
    function wantripInitMap() {{
      const options = {{
        center: {{ lat: {center_lat}, lng: {center_lng} }},
        zoom: {zoom},
        gestureHandling: "greedy",
        mapTypeControl: false,
        streetViewControl: false
      }};
      if (google.maps.ColorScheme) {{
        options.colorScheme = google.maps.ColorScheme.DARK;
      }}
      const map = new google.maps.Map(document.getElementById("map"), options);
      const bounds = new google.maps.LatLngBounds();
      const info = new google.maps.InfoWindow();
      places.forEach((place) => {{
        const position = {{ lat: place.lat, lng: place.lng }};
        bounds.extend(position);
        const marker = new google.maps.Marker({{
          map: map,
          position: position,
          title: place.name,
          icon: {{
            path: google.maps.SymbolPath.CIRCLE,
            scale: 9,
            fillColor: place.color,
            fillOpacity: 1,
            strokeColor: "#ffffff",
            strokeWeight: 2
          }}
        }});
        const link = place.url
          ? "<a href=\\"" + escapeHtml(place.url) + "\\" target=\\"_blank\\" rel=\\"noopener\\" style=\\"display:inline-block;margin-top:8px;color:#1967D2;font-size:14px;font-weight:400;line-height:1.5;text-decoration:underline;\\">Googleマップで開く</a>"
          : "";
        const dogDetails = (place.dogDetails || []).map((line) =>
          "<div style=\\"color:#444444;font-weight:400;font-size:14px;line-height:1.5;margin:2px 0 0;\\">" + escapeHtml(line) + "</div>"
        ).join("");
        marker.addListener("click", () => {{
          info.setContent(
            "<div style=\\"box-sizing:border-box;background:#FFFFFF;color:#202124;padding:4px 4px 8px;max-width:min(260px,72vw);font-family:Arial,sans-serif;line-height:1.5;\\">" +
            "<div style=\\"color:#202124;font-weight:700;font-size:16px;line-height:1.4;margin:0 0 6px;\\">" + escapeHtml(place.name) + "</div>" +
            "<div style=\\"color:#444444;font-weight:400;font-size:14px;line-height:1.5;margin:0 0 2px;\\">" + escapeHtml(place.category) + "</div>" +
            "<div style=\\"color:#444444;font-weight:400;font-size:14px;line-height:1.5;margin:0;\\">" + escapeHtml(place.address) + "</div>" +
            "<div style=\\"color:" + escapeHtml(place.dogStatusColor || "#444444") + ";font-weight:700;font-size:14px;line-height:1.5;margin:6px 0 0;\\">" + escapeHtml(place.dogStatus || "未確認") + "</div>" +
            dogDetails +
            link +
            "</div>"
          );
          info.open({{ map: map, anchor: marker }});
        }});
      }});
      if (places.length === 1) {{
        map.setCenter(bounds.getCenter());
        map.setZoom(15);
      }} else {{
        map.fitBounds(bounds, 48);
      }}
    }}
  </script>
  <script async defer src="{script_src}&callback=wantripInitMap" onerror="wantripMapError()"></script>
</body>
</html>
"""


def search_nearby(latitude, longitude, categories, api_key):
    """選んだ種別だけを、指定した中心と半径で Nearby Search する。"""
    chosen = selected_categories(categories)
    if not chosen:
        raise PlacesServiceError("希望する施設を、1つ以上選んでください。")
    if not api_key:
        raise PlacesServiceError(
            "Google Places API のキーが未設定です。"
            "環境変数 GOOGLE_PLACES_API_KEY か、.streamlit/secrets.toml の "
            "GOOGLE_PLACES_API_KEY を設定してください。"
        )
    body = {
        "includedTypes": list(included_types(chosen)),
        "maxResultCount": MAX_RESULT_COUNT,
        "languageCode": "ja",
        "regionCode": "JP",
        "rankPreference": "DISTANCE",
        "locationRestriction": {
            "circle": {
                "center": {
                    "latitude": latitude,
                    "longitude": longitude,
                },
                "radius": float(SEARCH_RADIUS_METERS),
            }
        },
    }
    try:
        response = requests.post(
            PLACES_SEARCH_URL,
            json=body,
            headers={
                "Content-Type": "application/json",
                "X-Goog-Api-Key": api_key,
                "X-Goog-FieldMask": PLACES_FIELD_MASK,
            },
            timeout=PLACES_TIMEOUT_SECONDS,
        )
    except requests.Timeout as error:
        raise PlacesServiceError(
            "施設検索の応答が時間内に返りませんでした。しばらくしてからもう一度試してください。"
        ) from error
    except requests.ConnectionError as error:
        raise PlacesServiceError(
            "施設検索のサーバーに接続できませんでした。ネットワーク接続を確認してください。"
        ) from error
    except requests.RequestException as error:
        raise PlacesServiceError(
            "施設検索に失敗しました。時間をおいてもう一度試してください。"
        ) from error

    if response.status_code in (401, 403):
        raise PlacesServiceError(
            "Google Places API のキーが拒否されました。キーと Places API (New) の有効化を確認してください。"
        )
    if response.status_code == 429:
        raise PlacesServiceError(
            "施設検索が一時的に制限されています。しばらく待ってからもう一度試してください。"
        )
    if response.status_code >= 400:
        raise PlacesServiceError(
            "施設検索に失敗しました。時間をおいてもう一度試してください。"
        )
    try:
        data = response.json()
    except ValueError as error:
        raise PlacesServiceError("施設の検索結果を読み取れませんでした。") from error
    return places_from_response(data, chosen)


def search_facilities(place_name, categories, api_key):
    """選択した目的地の代表点を中心に施設を探す。犬のサイズは使わない。"""
    latitude, longitude = LOCATIONS[place_name]
    places, attributions = search_nearby(
        latitude,
        longitude,
        selected_categories(categories),
        api_key,
    )
    return latitude, longitude, places, attributions


def places_session_cache():
    """開いている画面の間だけ、検索条件ごとの結果を覚える。

    キーは search_identity（地点、カテゴリー、中心座標、半径、施設種別）。
    Google Maps Platform の利用条件では、Place ID は保存でき、緯度・経度は
    連続30日まで一時保存できる。施設名・住所・地図URLは、以前の24時間キャッシュへ
    無条件には保存できない。このアプリはディスクにも st.cache_data にも書かず、
    ブラウザセッションのメモリだけに置く。
    """
    cache = st.session_state.get("places_session_cache")
    if not isinstance(cache, dict):
        cache = {}
        st.session_state["places_session_cache"] = cache
    return cache


def map_session_id():
    """この画面の間だけ使う地図用ID。再実行しても同じ値を保ち、推測しにくくする。"""
    current = st.session_state.get("wantrip_map_session_id")
    if isinstance(current, str) and _SESSION_ID_RE.fullmatch(current):
        return current
    current = secrets.token_hex(16)
    st.session_state["wantrip_map_session_id"] = current
    return current


def _map_html_name(session_id, token):
    """セッションIDと検索トークンだけでファイル名を決める。秘密情報は入れない。"""
    if not _SESSION_ID_RE.fullmatch(session_id) or not _SEARCH_TOKEN_RE.fullmatch(token):
        return None
    name = f"{MAP_FILE_PREFIX}-{session_id}-{token}.html"
    if not _MAP_FILE_RE.fullmatch(name):
        return None
    return name


def _map_file_path(session_id, name):
    """このセッションの地図HTMLだけを、static ディレクトリの直下に限って指す。"""
    if not isinstance(name, str) or not name.startswith(f"{MAP_FILE_PREFIX}-{session_id}-"):
        return None
    if not _MAP_FILE_RE.fullmatch(name):
        return None
    root = STATIC_DIR.resolve()
    path = (STATIC_DIR / name).resolve()
    if path.parent != root:
        return None
    return path


def _delete_previous_map(session_id, previous_name, current_name):
    """同じセッションの直前の地図HTMLだけを消す。他のセッションのファイルは触らない。"""
    if previous_name == current_name:
        return
    path = _map_file_path(session_id, previous_name)
    if path is None or not path.is_file():
        return
    path.unlink()


def places_map_url(places, maps_api_key):
    """このセッション専用の地図HTMLを static に書き、iframe 用のURLを返す。

    ファイル名は wantrip-map-<セッションID>-<検索トークン>.html。
    同じセッションで次の検索をしたときだけ、その直前のファイルを削除する。
    URLは /app/static/ で始まる。HTML文字列を iframe に渡すと about:srcdoc になる。
    """
    html = build_places_map_html(places, maps_api_key)
    if html is None:
        return None
    token_source = [
        {
            "place_id": record["place_id"],
            "name": record["name"],
            "address": record["address"],
            "latitude": record["latitude"],
            "longitude": record["longitude"],
            "google_maps_url": record["google_maps_url"],
            "dog_friendly_status": record["dog_friendly_status"],
            "dog_friendly_source": record["dog_friendly_source"],
            "dog_friendly_note": record["dog_friendly_note"],
            "dog_friendly_checked_at": record["dog_friendly_checked_at"],
        }
        for record in marker_records(places)
    ]
    token = hashlib.sha256(
        json.dumps(token_source, ensure_ascii=False, sort_keys=True).encode("utf-8")
    ).hexdigest()[:16]
    session_id = map_session_id()
    file_name = _map_html_name(session_id, token)
    target = _map_file_path(session_id, file_name) if file_name else None
    if target is None:
        return None
    STATIC_DIR.mkdir(parents=True, exist_ok=True)
    temporary = STATIC_DIR / f".{file_name}.{secrets.token_hex(8)}.tmp"
    previous_name = st.session_state.get("wantrip_map_html_name")
    try:
        temporary.write_text(html, encoding="utf-8")
        temporary.replace(target)
    except OSError:
        if temporary.is_file():
            try:
                temporary.unlink()
            except OSError:
                pass
        return None
    try:
        _delete_previous_map(session_id, previous_name, file_name)
    except OSError:
        pass
    st.session_state["wantrip_map_html_name"] = file_name
    return f"/app/static/{file_name}?v={token}"


def _render_places_map(places, maps_api_key):
    map_url = places_map_url(places, maps_api_key)
    if map_url is None:
        return False
    st.iframe(map_url, width="stretch", height=420)
    return True


st.set_page_config(
    page_title="WanTrip",
    page_icon="🐶",
    layout="centered",
)

st.title("🐶 WanTrip")
st.write("犬と一緒に行けるお出かけスポットを探すアプリです。")
st.info(
    "選んだ候補地の3日間の天気と、周辺約10kmの施設を表示できます。"
    "施設は選んだ種類だけ検索します。犬のサイズは、まだ検索条件にしていません。"
)

if not places_api_key():
    st.info(
        "施設検索には Google Places API のキーが必要です。"
        "環境変数 GOOGLE_PLACES_API_KEY、または .streamlit/secrets.toml の "
        "GOOGLE_PLACES_API_KEY を設定してください。キーが無くても天気は表示できます。"
    )

if not maps_api_key():
    st.info(
        "画面内の地図には Google Maps JavaScript API のキーが必要です。"
        "環境変数 GOOGLE_MAPS_API_KEY、または .streamlit/secrets.toml の "
        "GOOGLE_MAPS_API_KEY を設定してください。"
        "このキーが無くても、天気と施設の一覧は表示できます。"
    )

destination = st.selectbox(
    "目的地",
    options=list(LOCATIONS.keys()),
    help="候補地から選びます。選んだ地点の緯度・経度で天気と施設を問い合わせます。",
)

dog_size = st.selectbox(
    "犬のサイズ",
    options=DOG_SIZES,
    help="将来、施設の受け入れ条件に使うための欄です。今回の施設検索では使いません。",
)

facilities = st.multiselect(
    "希望する施設",
    options=FACILITY_TYPES,
    default=["ドッグラン"],
    help="初期状態はドッグランです。カフェや宿泊施設は施設の種類で検索し、犬の同伴可否は未確認と表示します。",
)

weather_column, search_column = st.columns(2)
with weather_column:
    fetch_weather = st.button(
        "天気を取得する",
        type="primary",
        use_container_width=True,
    )
with search_column:
    search_parks = st.button(
        "施設を検索する",
        use_container_width=True,
    )

if fetch_weather:
    if not facilities:
        st.session_state["form_warning"] = "希望する施設を、1つ以上選んでください。"
        st.session_state["weather_error"] = None
        st.session_state["weather_rows"] = None
        st.session_state["confirmed"] = None
    else:
        latitude, longitude = LOCATIONS[destination]
        rows, error = fetch_three_day_forecast(latitude, longitude)
        st.session_state["form_warning"] = None
        st.session_state["weather_error"] = error
        st.session_state["weather_rows"] = rows
        st.session_state["confirmed"] = {
            "place": destination,
            "latitude": latitude,
            "longitude": longitude,
            "dog_size": dog_size,
            "facilities": list(facilities),
        }

if search_parks:
    chosen = selected_categories(facilities)
    if not chosen:
        st.session_state["dog_park_error"] = "希望する施設を、1つ以上選んでください。"
        st.session_state["dog_parks"] = None
        st.session_state["dog_park_search"] = None
    else:
        identity = search_identity(destination, chosen)
        cache_key = json.dumps(identity, ensure_ascii=False)
        try:
            record = places_session_cache().get(cache_key)
            if record is None:
                with st.spinner("施設を検索しています..."):
                    center_lat, center_lon, parks, attributions = search_facilities(
                        destination,
                        chosen,
                        places_api_key(),
                    )
                record = {
                    "latitude": center_lat,
                    "longitude": center_lon,
                    "places": parks,
                    "attributions": attributions,
                }
                places_session_cache()[cache_key] = record
        except PlacesServiceError as error:
            st.session_state["dog_park_error"] = str(error)
            st.session_state["dog_parks"] = None
            st.session_state["dog_park_search"] = None
        else:
            st.session_state["dog_park_error"] = None
            st.session_state["dog_parks"] = record["places"]
            st.session_state["dog_park_search"] = {
                "place": destination,
                "latitude": record["latitude"],
                "longitude": record["longitude"],
                "categories": list(chosen),
                "identity": identity,
                "attributions": record["attributions"],
            }

form_warning = st.session_state.get("form_warning")
if form_warning:
    st.warning(form_warning)

confirmed = st.session_state.get("confirmed")
if confirmed:
    st.success("天気の条件を受け取りました。")
    st.write(f"**目的地:** {confirmed['place']}")
    st.write(f"**犬のサイズ:** {confirmed['dog_size']}")
    st.write(f"**希望する施設:** {'、'.join(confirmed['facilities'])}")
    st.caption(
        f"天気の問い合わせ地点: 北緯 {confirmed['latitude']:.5f} / 東経 {confirmed['longitude']:.5f}"
    )

weather_error = st.session_state.get("weather_error")
if weather_error:
    st.error(weather_error)

weather_rows = st.session_state.get("weather_rows")
if weather_rows:
    place_name = confirmed["place"] if confirmed else "選択した地点"
    st.subheader(f"{place_name}の今後3日間")
    st.caption("天気、最高気温（℃）、その日の降水確率の最大値です。出典: Open-Meteo")
    # 色は指定しない。Streamlitのダークテーマの文字色と背景のまま使う。
    st.markdown(
        """
        <style>
        .wantrip-emoji { font-size: 2.2rem; line-height: 1.2; margin: 0; }
        </style>
        """,
        unsafe_allow_html=True,
    )
    day_columns = st.columns(len(weather_rows))
    for column, row in zip(day_columns, weather_rows):
        with column:
            with st.container(border=True):
                st.markdown(
                    f"<p class='wantrip-emoji'>{row.get('emoji', '❓')}</p>",
                    unsafe_allow_html=True,
                )
                st.markdown(f"**{row.get('label', '天気不明')}**")
                st.caption(format_forecast_date(row["date"]))
                st.metric("最高気温", f"{row['temp_max']:.1f} ℃")
                st.metric("降水確率", f"{row['precip_prob']:.0f} %")

dog_park_error = st.session_state.get("dog_park_error")
if dog_park_error:
    st.error(dog_park_error)

dog_parks = st.session_state.get("dog_parks")
dog_park_search = st.session_state.get("dog_park_search")
if dog_park_search and dog_parks is not None:
    categories = dog_park_search.get("categories") or ["ドッグラン"]
    category_label = "・".join(categories)
    st.subheader(f"{dog_park_search['place']}周辺の{category_label}")
    st.caption(
        f"検索の中心から約{SEARCH_RADIUS_METERS // 1000}km、最大{MAX_RESULT_COUNT}件です。"
        "犬の同伴可否は、公式情報で確認できた施設だけを表示します。"
        "確認情報がない施設は「未確認」です。"
        f"中心: 北緯 {dog_park_search['latitude']:.5f} / "
        f"東経 {dog_park_search['longitude']:.5f}"
    )
    if not dog_parks:
        st.warning(
            f"周辺の{category_label}が見つかりませんでした。"
            "Google Maps に登録されていない可能性があります。"
        )
    else:
        st.write(f"{len(dog_parks)}件見つかりました。")
        dog_filter = st.radio(
            "犬同伴の絞り込み",
            options=DOG_FILTERS,
            index=0,
            horizontal=True,
            key="dog_status_filter",
        )
        visible_parks = filter_places_by_dog_status(dog_parks, dog_filter)
        st.write(f"{len(dog_parks)}件中、{len(visible_parks)}件を表示しています。")
        if len(dog_parks) < 3 or len(dog_parks) >= MAX_RESULT_COUNT:
            st.caption(
                "件数が少ない、または上限に達している場合は、"
                "Google Maps への登録状況によって見つからないことがあります。"
            )
        if not visible_parks:
            st.info("この絞り込みに合う施設はありません。")
        else:
            records = marker_records(visible_parks)
            skipped = len(visible_parks) - len(records)
            if not records:
                st.warning(
                    "施設の緯度・経度が取得できなかったため、地図上のマーカーは表示できません。"
                )
            else:
                if skipped:
                    st.caption(
                        f"{skipped}件は緯度・経度がないため、地図のマーカーにしていません。"
                    )
                map_key = maps_api_key()
                if not map_key:
                    st.error(
                        "地図を表示できません。Google Maps JavaScript API のキーが未設定です。"
                        "環境変数 GOOGLE_MAPS_API_KEY か、.streamlit/secrets.toml の "
                        "GOOGLE_MAPS_API_KEY を設定してください。"
                    )
                elif not _render_places_map(visible_parks, map_key):
                    st.error(
                        "地図を表示できませんでした。下の一覧からGoogleマップを開いてください。"
                    )
            for park in visible_parks:
                dog_view = dog_status_view(park)
                with st.container(border=True):
                    st.markdown(f"**{park['name']}**")
                    st.write(f"カテゴリー: {park.get('category', '')}")
                    if park.get("address"):
                        st.write(f"住所: {park['address']}")
                    else:
                        st.write("住所: 登録なし")
                    st.write(f"犬の同伴: {dog_view['label']}")
                    for detail in dog_view["details"]:
                        st.write(detail)
                    if park.get("google_maps_url"):
                        st.markdown(
                            f"[Googleマップで位置を確認する]({park['google_maps_url']})"
                        )
                    else:
                        st.write("Googleマップのリンク: 取得できませんでした")
        st.caption("施設情報の出典: Google Maps")
        provider_names = dog_park_search.get("attributions") or []
        if provider_names:
            st.caption("データの提供: " + "、".join(provider_names))
