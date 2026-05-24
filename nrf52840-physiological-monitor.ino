#include <Arduino.h>
#include <Wire.h>
#include <SPI.h>

#define USE_TFT_ESPI_LIBRARY
#include "lv_xiao_round_screen.h"
#include "lvgl.h"

#include "RTClib.h"
#include "SdFat.h"
#include <LSM6DS3.h>
#include <MAX30105.h>
#include "spo2_algorithm.h"

// ================================================================
//  КОНСТАНТЫ
// ================================================================
#define WDT_TIMEOUT_MS        8000
#define FUNCTION_TIMEOUT_MS   5000
#define VIBRATION_MOTOR_PIN   D0
#define SD_CS_PIN             D2
#define MAX_ALARMS            5
#define MAX_HISTORY           20
#define MAX_PEAKS             50

// Датчик работает на 100 Hz → период сэмпла 10 мс
#define SENSOR_FS             100
#define SENSOR_PERIOD_MS      10

// Скользящее окно 15 секунд
#define SLIDING_WINDOW_SIZE   1500

// Пересчёт ЧД/ВСР каждые 10 секунд
#define CALC_INTERVAL_MS      10000

// Запись пульса в лог не чаще раза в минуту
#define HR_LOG_INTERVAL_MS    60000UL

// Запись ЧД/ВСР в лог не чаще раза в 10 минут
#define RESP_HRV_LOG_INTERVAL_MS  600000UL

// ================================================================
//  СТРУКТУРЫ
// ================================================================
struct Alarm {
    uint8_t hour;
    uint8_t minute;
    bool    enabled;
};

// ================================================================
//  ГЛОБАЛЬНЫЕ ОБЪЕКТЫ
// ================================================================
RTC_PCF8563 rtc;
SdFat       SD;
MAX30105    particleSensor;
LSM6DS3     myIMU(I2C_MODE, 0x6A);

// ================================================================
//  БУФЕРЫ ИЗМЕРЕНИЙ
// ================================================================
uint32_t irBuffer[BUFFER_SIZE];
uint32_t redBuffer[BUFFER_SIZE];
int      bufferIndex = 0;

uint32_t slidingIrBuf[SLIDING_WINDOW_SIZE];
int      slidingBufHead = 0;
bool     slidingBufFull = false;

static uint32_t linearBuf[SLIDING_WINDOW_SIZE];

int32_t n_spo2       = 0;
int32_t n_heart_rate = 0;
int8_t  spo2_valid   = 0;
int8_t  hr_valid     = 0;

unsigned long sampleCount    = 0;
unsigned long lastSampleTime = 0;

static int            sensorErrorStreak = 0;
static unsigned long  lastI2CCheck      = 0;
const  unsigned long  I2C_CHECK_INTERVAL = 5000UL;

// ================================================================
//  ИСТОРИЯ ЧД И ВСР
// ================================================================
float         respHistory[MAX_HISTORY];
float         hrvHistory[MAX_HISTORY];
unsigned long historyTimestamps[MAX_HISTORY];
int           historyIndex = 0;

static float ac_buf[SLIDING_WINDOW_SIZE];
static float env_buf[SLIDING_WINDOW_SIZE];

int respRate = 0;
int hrvValue = 0;

bool hasValidResp = false;
bool hasValidHRV  = false;

unsigned long lastCalcTime       = 0;
unsigned long lastHRLogTime      = 0;
unsigned long lastRespHRVLogTime = 0;

int  displayRespRate = 0;
int  displayHRVValue = 0;
bool hasDisplayResp  = false;
bool hasDisplayHRV   = false;

// ================================================================
//  ФЛАГИ
// ================================================================
volatile bool respGraphNeedsUpdate = false;
volatile bool hrvGraphNeedsUpdate  = false;

// ================================================================
//  WDT
// ================================================================
volatile bool          wdt_armed           = false;
volatile unsigned long last_wdt_feed       = 0;
unsigned long          function_entry_time = 0;

// ================================================================
//  БУДИЛЬНИКИ
// ================================================================
Alarm alarms[MAX_ALARMS];

// ================================================================
//  LVGL — ЭКРАНЫ
// ================================================================
static lv_obj_t *scr_main;
static lv_obj_t *scr_heart;
static lv_obj_t *scr_alarm_list;
static lv_obj_t *scr_alarm_set;
static lv_obj_t *scr_alarm_ring;
static lv_obj_t *scr_hr_log;
static lv_obj_t *scr_breath_hrv;
static lv_obj_t *scr_resp_graph;
static lv_obj_t *scr_hrv_graph;

// ================================================================
//  LVGL — ВИДЖЕТЫ ГЛАВНОГО ЭКРАНА
// ================================================================
static lv_obj_t *label_time;
static lv_obj_t *label_battery;
static lv_obj_t *label_date;
static lv_obj_t *label_last_hr;
static lv_obj_t *label_steps;
static lv_obj_t *label_alarm;

// ================================================================
//  LVGL — ВИДЖЕТЫ ЭКРАНА ПУЛЬСА
// ================================================================
static lv_obj_t *label_hr_value;
static lv_obj_t *label_spo2;
static lv_obj_t *bar;
static lv_obj_t *btn_measure;
static lv_obj_t *label_status;

// ================================================================
//  LVGL — ВИДЖЕТЫ ГРАФИКА ПУЛЬСА
// ================================================================
static lv_obj_t          *hr_chart;
static lv_chart_series_t *hr_series;
static lv_obj_t          *hr_range_label;
static lv_obj_t          *x_label_0;
static lv_obj_t          *x_label_6;
static lv_obj_t          *x_label_12;
static lv_obj_t          *x_label_18;
static lv_obj_t          *y_label_min;
static lv_obj_t          *y_label_max;

// ================================================================
//  LVGL — ВИДЖЕТЫ БУДИЛЬНИКА
// ================================================================
static lv_obj_t *btn_stop_alarm;
static lv_obj_t *roller_hour;
static lv_obj_t *roller_min;
static lv_obj_t *label_alarm_time;

// Контейнеры строк (по одному на слот будильника)
static lv_obj_t *alarm_rows[MAX_ALARMS];

// Метки времени будильников
static lv_obj_t *alarm_time_labels[MAX_ALARMS];

// Переключатели вкл/выкл
static lv_obj_t *alarm_switches[MAX_ALARMS];

// Кнопки удаления
static lv_obj_t *alarm_del_btns[MAX_ALARMS];

// Кнопка добавления
static lv_obj_t *btn_add_alarm;

// ================================================================
//  LVGL — ВИДЖЕТЫ ЭКРАНА ЧД/ВСР
// ================================================================
static lv_obj_t *label_resp_rate;
static lv_obj_t *label_hrv_value;
static lv_obj_t *btn_resp_graph;
static lv_obj_t *btn_hrv_graph;

// ================================================================
//  LVGL — ВИДЖЕТЫ ГРАФИКА ЧД
// ================================================================
static lv_obj_t          *resp_chart;
static lv_chart_series_t *resp_series;
static lv_obj_t          *resp_range_label;
static lv_obj_t          *resp_x_label_0;
static lv_obj_t          *resp_x_label_6;
static lv_obj_t          *resp_x_label_12;
static lv_obj_t          *resp_x_label_18;
static lv_obj_t          *resp_y_label_min;
static lv_obj_t          *resp_y_label_max;

// ================================================================
//  LVGL — ВИДЖЕТЫ ГРАФИКА ВСР
// ================================================================
static lv_obj_t          *hrv_chart;
static lv_chart_series_t *hrv_series;
static lv_obj_t          *hrv_range_label;
static lv_obj_t          *hrv_x_label_0;
static lv_obj_t          *hrv_x_label_6;
static lv_obj_t          *hrv_x_label_12;
static lv_obj_t          *hrv_x_label_18;
static lv_obj_t          *hrv_y_label_min;
static lv_obj_t          *hrv_y_label_max;

// ================================================================
//  СОСТОЯНИЕ ПРИЛОЖЕНИЯ
// ================================================================
bool displayOn          = true;
int  currentScreen      = 0;
bool alarmActive        = false;
int  hrValue            = 0;
int  spo2Value          = 0;
int  stepCount          = 0;
int  lastDay            = -1;
int  todayMinBPM        = 999;
int  todayMaxBPM        = 0;
int  editHour           = 0;
int  editMinute         = 0;
bool imu_initialized    = false;
bool sensor_initialized = false;

// ================================================================
//  ВИБРАЦИЯ И БУДИЛЬНИК
// ================================================================
bool          vibrationActive    = false;
unsigned long vibrationStartTime = 0;
unsigned long alarmRingStartTime = 0;
int           ringingAlarmIndex  = -1;
const unsigned long alarmRingDuration = 20000UL;

// ================================================================
//  ИЗМЕРЕНИЕ
// ================================================================
bool          isMeasuring               = false;
unsigned long measurementStart          = 0;
bool          autoMeasurementInProgress = false;
unsigned long lastAutoMeasureTime       = 0;
const unsigned long AUTO_MEASURE_INTERVAL = 60000UL;
const unsigned long AUTO_MAX_SAMPLES      = 3000UL;

static float irFiltered  = 0.0f;
static float redFiltered = 0.0f;
static int   hrAvg       = 0;
static int   lastHR      = 0;

static uint32_t prevIR  = 0;
static uint32_t prevRed = 0;

// ================================================================
//  ШАГОМЕР
// ================================================================
const float         FILTER_COEF       = 0.1f;
float               accX_f            = 0.0f;
float               accY_f            = 0.0f;
float               accZ_f            = 0.0f;
float               gyroX             = 0.0f;
float               gyroY             = 0.0f;
float               gyroZ             = 0.0f;
float               rawAccX           = 0.0f;
float               rawAccY           = 0.0f;
float               rawAccZ           = 0.0f;
unsigned long       lastStepTime      = 0;
bool                peakDetected      = false;
float               accMagFiltered    = 0.0f;
float               baseline          = 1.0f;
const float         STEP_DELTA        = 0.09f;
const float         HYSTERESIS        = 0.08f;
const unsigned long MIN_STEP_INTERVAL = 250UL;
const float         GYRO_LIMIT        = 250.0f;

// ================================================================
//  BACKUP
// ================================================================
unsigned long lastBackupTime = 0;
const unsigned long BACKUP_INTERVAL = 60000UL;

// ================================================================
//  ПРОТОТИПЫ
// ================================================================
void setupRTC();
void setupUI();
void createAlarmListScreen();
void createAlarmSetScreen();
void createAlarmRingScreen();
void createHRLogScreen();
void createBreathHRVScreen();
void createRespGraphScreen();
void createHRVGraphScreen();

void updateHRChart();
void updateAlarmList();
void updateUIValues();
void updateBreathHRVScreen();
void updateHRDisplay();
void updateRespGraph();
void updateHRVGraph();

void handleGesture();
void checkAlarm();
void checkDayReset();
void updateMeasurement();
void stopMeasurement(bool success);
void resetMeasurementState();
void calcRespAndHRV();
void logHRToSD();
void logRespHRVToSD();

void readIMU();
void updateStepCounter();
void autoMeasureHeartRate();
void handleVibration();

void saveBackup();
void loadBackup();
void armWDT();
void feedWDT();
void markFunctionEntry();
bool checkFunctionTimeout(const char *func_name);
int  batteryLevelPercent();
bool isFingerOnSensor();
bool isNewSample();
bool recoverI2CBus();
bool initSensor();
bool readSensor(uint32_t &ir, uint32_t &red);
void sensorSleep();
void sensorWakeUp();

int   findPeaks(uint32_t *buffer, int length, int *peaks, int minDistance, int maxPeaks);
int   findPeaksFloat(float *buffer, int length, int *peaks, int minDistance, int maxPeaks);
float computeRespiratoryRate(uint32_t *buf, int fs, int length);
float computeHRV(int *peaks, int peakCount, int fs);

static void btnMeasureHandler(lv_event_t *e);
static void swipeEventHandler(lv_event_t *e);
static void alarmSwitchHandler(lv_event_t *e);
static void btnAddAlarmHandler(lv_event_t *e);
static void btnSetAlarmHandler(lv_event_t *e);
static void btnDelAlarmHandler(lv_event_t *e);

// ================================================================
//  SETUP
// ================================================================
void setup() {
    NRF_WDT->CONFIG = 0x01;
    NRF_WDT->CRV    = (WDT_TIMEOUT_MS * 32768) / 1000 + 1;
    NRF_WDT->RREN   = 0x01;

    Serial.begin(115200);
    delay(1000);

    pinMode(D6, OUTPUT);
    digitalWrite(D6, HIGH);
    pinMode(VIBRATION_MOTOR_PIN, OUTPUT);
    digitalWrite(VIBRATION_MOTOR_PIN, LOW);

    Wire.begin();
    Wire.setClock(400000);
    delay(100);

    markFunctionEntry();
    lv_init();
    lv_xiao_disp_init();
    lv_xiao_touch_init();
    checkFunctionTimeout("lv_init");

    markFunctionEntry();
    if (myIMU.begin() != 0) {
        Serial.println("IMU FAILED");
        imu_initialized = false;
    } else {
        Serial.println("IMU OK");
        imu_initialized = true;
    }
    checkFunctionTimeout("IMU");

    markFunctionEntry();
    if (!particleSensor.begin(Wire, I2C_SPEED_FAST)) {
        Serial.println("MAX30102 not found");
        sensor_initialized = false;
    } else {
        Serial.println("MAX30102 OK");
        sensor_initialized = true;
        particleSensor.setup(0x1F, 1, 2, 100, 411, 4096);
        particleSensor.setPulseAmplitudeRed(0x1F);
        particleSensor.setPulseAmplitudeIR(0x1F);
        particleSensor.setPulseAmplitudeGreen(0);
        particleSensor.clearFIFO();
        particleSensor.shutDown();
    }
    checkFunctionTimeout("MAX30102");

    markFunctionEntry();
    setupRTC();
    checkFunctionTimeout("RTC");

    markFunctionEntry();
    if (!SD.begin(SD_CS_PIN)) {
        Serial.println("SD Card failed");
    }
    checkFunctionTimeout("SD");

    for (int i = 0; i < MAX_HISTORY; i++) {
        respHistory[i]       = 0.0f;
        hrvHistory[i]        = 0.0f;
        historyTimestamps[i] = 0;
    }
    historyIndex = 0;

    loadBackup();

    DateTime now = rtc.now();
    lastDay = now.day();

    markFunctionEntry();
    setupUI();
    checkFunctionTimeout("setupUI");

    armWDT();
    Serial.println("Setup complete");
}

// ================================================================
//  LOOP
// ================================================================
void loop() {
    feedWDT();

    lv_timer_handler();

    markFunctionEntry();
    checkDayReset();
    checkFunctionTimeout("checkDayReset");

    markFunctionEntry();
    handleGesture();
    checkFunctionTimeout("handleGesture");

    markFunctionEntry();
    checkAlarm();
    checkFunctionTimeout("checkAlarm");

    markFunctionEntry();
    updateMeasurement();
    checkFunctionTimeout("updateMeasurement");

    markFunctionEntry();
    updateStepCounter();
    checkFunctionTimeout("updateStepCounter");

    autoMeasureHeartRate();

    if (millis() - lastBackupTime >= BACKUP_INTERVAL) {
        lastBackupTime = millis();
        saveBackup();
    }

    static unsigned long lastUIUpdate = 0;
    if (millis() - lastUIUpdate > 1000UL) {
        lastUIUpdate = millis();
        markFunctionEntry();
        updateUIValues();
        checkFunctionTimeout("updateUIValues");
    }

    if (respGraphNeedsUpdate) {
        updateRespGraph();
        respGraphNeedsUpdate = false;
    }
    if (hrvGraphNeedsUpdate) {
        updateHRVGraph();
        hrvGraphNeedsUpdate = false;
    }

    handleVibration();
}

// ================================================================
//  ДЕТЕКЦИЯ НОВОГО СЭМПЛА
// ================================================================
bool isNewSample() {
    if (!sensor_initialized) return false;
    uint32_t ir  = particleSensor.getIR();
    uint32_t red = particleSensor.getRed();
    if (ir == prevIR && red == prevRed) return false;
    prevIR  = ir;
    prevRed = red;
    return true;
}

// ================================================================
//  RTC
// ================================================================
void setupRTC() {
    if (!rtc.begin()) {
        Serial.println("RTC failed");
        while (1) {}
    }
    if (rtc.lostPower()) {
        rtc.adjust(DateTime(F(__DATE__), F(__TIME__)));
    }
}

// ================================================================
//  UI
// ================================================================
void setupUI() {
    scr_main  = lv_obj_create(NULL);
    scr_heart = lv_obj_create(NULL);

    createAlarmListScreen();
    createAlarmSetScreen();
    createAlarmRingScreen();
    createHRLogScreen();
    createBreathHRVScreen();
    createRespGraphScreen();
    createHRVGraphScreen();

    // ---- Главный экран ----
    lv_obj_set_style_bg_color(scr_main,
        lv_color_hex(0x1A1A2E), LV_STATE_DEFAULT);

    label_battery = lv_label_create(scr_main);
    lv_obj_align(label_battery, LV_ALIGN_TOP_MID, 0, 10);
    lv_obj_set_style_text_color(label_battery,
        lv_color_white(), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(label_battery,
        &lv_font_montserrat_18, LV_STATE_DEFAULT);

    label_time = lv_label_create(scr_main);
    lv_obj_align(label_time, LV_ALIGN_CENTER, 0, -40);
    lv_obj_set_style_text_font(label_time,
        &lv_font_montserrat_48, LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(label_time,
        lv_color_white(), LV_STATE_DEFAULT);

    label_date = lv_label_create(scr_main);
    lv_obj_align(label_date, LV_ALIGN_CENTER, 0, 0);
    lv_obj_set_style_text_color(label_date,
        lv_color_white(), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(label_date,
        &lv_font_montserrat_20, LV_STATE_DEFAULT);

    label_last_hr = lv_label_create(scr_main);
    lv_obj_align(label_last_hr, LV_ALIGN_CENTER, 0, 40);
    lv_obj_set_style_text_color(label_last_hr,
        lv_color_white(), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(label_last_hr,
        &lv_font_montserrat_18, LV_STATE_DEFAULT);

    label_steps = lv_label_create(scr_main);
    lv_obj_align(label_steps, LV_ALIGN_CENTER, 0, 70);
    lv_obj_set_style_text_color(label_steps,
        lv_color_white(), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(label_steps,
        &lv_font_montserrat_18, LV_STATE_DEFAULT);

    label_alarm = lv_label_create(scr_main);
    lv_obj_align(label_alarm, LV_ALIGN_BOTTOM_MID, 0, -10);
    lv_obj_set_style_text_color(label_alarm,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(label_alarm,
        &lv_font_montserrat_14, LV_STATE_DEFAULT);

    // ---- Экран пульса ----
    lv_obj_set_style_bg_color(scr_heart,
        lv_color_hex(0x1A1A2E), LV_STATE_DEFAULT);

    lv_obj_t *title_hr = lv_label_create(scr_heart);
    lv_label_set_text(title_hr, "Heart Rate / SpO2");
    lv_obj_align(title_hr, LV_ALIGN_TOP_MID, 0, 20);
    lv_obj_set_style_text_color(title_hr,
        lv_color_white(), LV_STATE_DEFAULT);

    bar = lv_bar_create(scr_heart);
    lv_obj_set_size(bar, 200, 15);
    lv_obj_align(bar, LV_ALIGN_CENTER, 0, -25);
    lv_bar_set_range(bar, 0, 100);
    lv_bar_set_value(bar, 0, LV_ANIM_OFF);
    lv_obj_set_style_bg_color(bar,
        lv_color_hex(0x333333), LV_PART_MAIN);
    lv_obj_set_style_bg_opa(bar, 255, LV_PART_MAIN);
    lv_obj_set_style_bg_color(bar,
        lv_color_hex(0x00FF88), LV_PART_INDICATOR);

    label_hr_value = lv_label_create(scr_heart);
    lv_label_set_text(label_hr_value, "-- bpm");
    lv_obj_align(label_hr_value, LV_ALIGN_CENTER, 0, 5);
    lv_obj_set_style_text_font(label_hr_value,
        &lv_font_montserrat_26, LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(label_hr_value,
        lv_color_white(), LV_STATE_DEFAULT);

    label_spo2 = lv_label_create(scr_heart);
    lv_label_set_text(label_spo2, "-- %");
    lv_obj_align(label_spo2, LV_ALIGN_CENTER, 0, 35);
    lv_obj_set_style_text_font(label_spo2,
        &lv_font_montserrat_22, LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(label_spo2,
        lv_color_white(), LV_STATE_DEFAULT);

    label_status = lv_label_create(scr_heart);
    lv_obj_align(label_status, LV_ALIGN_CENTER, 0, 75);
    lv_obj_set_style_text_color(label_status,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_label_set_text(label_status, "");

    btn_measure = lv_btn_create(scr_heart);
    lv_obj_align(btn_measure, LV_ALIGN_BOTTOM_MID, 0, -20);
    lv_obj_t *btn_label = lv_label_create(btn_measure);
    lv_label_set_text(btn_label, "Measure");
    lv_obj_add_event_cb(btn_measure,
        btnMeasureHandler, LV_EVENT_CLICKED, NULL);

    // ---- Жесты ----
    lv_obj_add_event_cb(scr_main,
        swipeEventHandler, LV_EVENT_GESTURE, NULL);
    lv_obj_add_event_cb(scr_heart,
        swipeEventHandler, LV_EVENT_GESTURE, NULL);
    lv_obj_add_event_cb(scr_hr_log,
        swipeEventHandler, LV_EVENT_GESTURE, NULL);
    lv_obj_add_event_cb(scr_alarm_list,
        swipeEventHandler, LV_EVENT_GESTURE, NULL);
    lv_obj_add_event_cb(scr_alarm_set,
        swipeEventHandler, LV_EVENT_GESTURE, NULL);
    lv_obj_add_event_cb(scr_breath_hrv,
        swipeEventHandler, LV_EVENT_GESTURE, NULL);
    lv_obj_add_event_cb(scr_resp_graph,
        swipeEventHandler, LV_EVENT_GESTURE, NULL);
    lv_obj_add_event_cb(scr_hrv_graph,
        swipeEventHandler, LV_EVENT_GESTURE, NULL);

    lv_scr_load(scr_main);
    currentScreen = 0;
}

// ================================================================
//  ЭКРАН ИСТОРИИ ПУЛЬСА
// ================================================================
void createHRLogScreen() {
    scr_hr_log = lv_obj_create(NULL);
    lv_obj_set_style_bg_color(scr_hr_log,
        lv_color_hex(0x1A1A2E), LV_STATE_DEFAULT);

    lv_obj_t *title = lv_label_create(scr_hr_log);
    lv_label_set_text(title, "Heart Rate Today");
    lv_obj_align(title, LV_ALIGN_TOP_MID, 0, 20);
    lv_obj_set_style_text_color(title,
        lv_color_white(), LV_STATE_DEFAULT);

    hr_chart = lv_chart_create(scr_hr_log);
    lv_obj_set_size(hr_chart, 180, 100);
    lv_obj_align(hr_chart, LV_ALIGN_CENTER, 10, -10);
    lv_chart_set_type(hr_chart, LV_CHART_TYPE_SCATTER);
    lv_chart_set_range(hr_chart,
        LV_CHART_AXIS_PRIMARY_Y, 40, 200);
    lv_chart_set_range(hr_chart,
        LV_CHART_AXIS_PRIMARY_X, 0, 23);
    lv_chart_set_point_count(hr_chart, 24);
    lv_obj_set_style_bg_color(hr_chart,
        lv_color_hex(0x1A1A2E), LV_PART_MAIN);
    lv_obj_set_style_bg_opa(hr_chart, 255, LV_PART_MAIN);
    lv_obj_set_style_line_color(hr_chart,
        lv_color_hex(0x333333), LV_PART_MAIN);
    lv_obj_set_style_border_width(hr_chart, 0, LV_PART_MAIN);

    // Серия создаётся ОДИН РАЗ
    hr_series = lv_chart_add_series(
        hr_chart,
        lv_color_hex(0x00FF88),
        LV_CHART_AXIS_PRIMARY_Y
    );

    // Инициализируем все 24 точки как NONE
    for (int h = 0; h < 24; h++) {
        lv_chart_set_value_by_id2(
            hr_chart, hr_series,
            h, h, LV_CHART_POINT_NONE
        );
    }
    lv_chart_refresh(hr_chart);

    // Подписи оси X
    x_label_0 = lv_label_create(scr_hr_log);
    lv_label_set_text(x_label_0, "0");
    lv_obj_align_to(x_label_0, hr_chart,
        LV_ALIGN_BOTTOM_LEFT, -5, 25);
    lv_obj_set_style_text_color(x_label_0,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(x_label_0,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    x_label_6 = lv_label_create(scr_hr_log);
    lv_label_set_text(x_label_6, "6");
    lv_obj_align_to(x_label_6, hr_chart,
        LV_ALIGN_BOTTOM_MID, -40, 25);
    lv_obj_set_style_text_color(x_label_6,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(x_label_6,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    x_label_12 = lv_label_create(scr_hr_log);
    lv_label_set_text(x_label_12, "12");
    lv_obj_align_to(x_label_12, hr_chart,
        LV_ALIGN_BOTTOM_MID, 0, 25);
    lv_obj_set_style_text_color(x_label_12,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(x_label_12,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    x_label_18 = lv_label_create(scr_hr_log);
    lv_label_set_text(x_label_18, "18");
    lv_obj_align_to(x_label_18, hr_chart,
        LV_ALIGN_BOTTOM_RIGHT, -35, 25);
    lv_obj_set_style_text_color(x_label_18,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(x_label_18,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    // Подписи оси Y
    y_label_min = lv_label_create(scr_hr_log);
    lv_label_set_text(y_label_min, "");
    lv_obj_align_to(y_label_min, hr_chart,
        LV_ALIGN_BOTTOM_LEFT, -27, 10);
    lv_obj_set_style_text_color(y_label_min,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(y_label_min,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    y_label_max = lv_label_create(scr_hr_log);
    lv_label_set_text(y_label_max, "");
    lv_obj_align_to(y_label_max, hr_chart,
        LV_ALIGN_TOP_LEFT, -27, -8);
    lv_obj_set_style_text_color(y_label_max,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(y_label_max,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    // Подпись диапазона
    hr_range_label = lv_label_create(scr_hr_log);
    lv_label_set_text(hr_range_label, "-- - -- bpm");
    lv_obj_align(hr_range_label, LV_ALIGN_BOTTOM_MID, 0, -20);
    lv_obj_set_style_text_color(hr_range_label,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
}

// ================================================================
//  ЭКРАН ЧД/ВСР
// ================================================================
void createBreathHRVScreen() {
    scr_breath_hrv = lv_obj_create(NULL);
    lv_obj_set_style_bg_color(scr_breath_hrv,
        lv_color_hex(0x1A1A2E), LV_STATE_DEFAULT);

    lv_obj_t *title = lv_label_create(scr_breath_hrv);
    lv_label_set_text(title, "Breathing & HRV");
    lv_obj_align(title, LV_ALIGN_TOP_MID, 0, 15);
    lv_obj_set_style_text_color(title,
        lv_color_white(), LV_STATE_DEFAULT);

    lv_obj_t *label_resp_title = lv_label_create(scr_breath_hrv);
    lv_label_set_text(label_resp_title, "Respiratory rate");
    lv_obj_align(label_resp_title, LV_ALIGN_TOP_LEFT, 20, 50);
    lv_obj_set_style_text_color(label_resp_title,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(label_resp_title,
        &lv_font_montserrat_14, LV_STATE_DEFAULT);

    label_resp_rate = lv_label_create(scr_breath_hrv);
    lv_label_set_text(label_resp_rate, "-- brpm");
    lv_obj_align(label_resp_rate, LV_ALIGN_TOP_LEFT, 20, 75);
    lv_obj_set_style_text_font(label_resp_rate,
        &lv_font_montserrat_28, LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(label_resp_rate,
        lv_color_white(), LV_STATE_DEFAULT);

    btn_resp_graph = lv_btn_create(scr_breath_hrv);
    lv_obj_set_size(btn_resp_graph, 80, 35);
    lv_obj_align(btn_resp_graph, LV_ALIGN_TOP_RIGHT, -20, 75);
    lv_obj_t *lbl_rg = lv_label_create(btn_resp_graph);
    lv_label_set_text(lbl_rg, "Graph");
    lv_obj_center(lbl_rg);
    lv_obj_add_event_cb(btn_resp_graph, [](lv_event_t *e) {
        updateRespGraph();
        lv_scr_load(scr_resp_graph);
        currentScreen = 8;
    }, LV_EVENT_CLICKED, NULL);

    lv_obj_t *label_hrv_title = lv_label_create(scr_breath_hrv);
    lv_label_set_text(label_hrv_title, "Heart Rate Variability");
    lv_obj_align(label_hrv_title, LV_ALIGN_TOP_LEFT, 20, 130);
    lv_obj_set_style_text_color(label_hrv_title,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(label_hrv_title,
        &lv_font_montserrat_14, LV_STATE_DEFAULT);

    label_hrv_value = lv_label_create(scr_breath_hrv);
    lv_label_set_text(label_hrv_value, "-- ms");
    lv_obj_align(label_hrv_value, LV_ALIGN_TOP_LEFT, 20, 155);
    lv_obj_set_style_text_font(label_hrv_value,
        &lv_font_montserrat_28, LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(label_hrv_value,
        lv_color_white(), LV_STATE_DEFAULT);

    btn_hrv_graph = lv_btn_create(scr_breath_hrv);
    lv_obj_set_size(btn_hrv_graph, 80, 35);
    lv_obj_align(btn_hrv_graph, LV_ALIGN_TOP_RIGHT, -20, 150);
    lv_obj_t *lbl_hg = lv_label_create(btn_hrv_graph);
    lv_label_set_text(lbl_hg, "Graph");
    lv_obj_center(lbl_hg);
    lv_obj_add_event_cb(btn_hrv_graph, [](lv_event_t *e) {
        updateHRVGraph();
        lv_scr_load(scr_hrv_graph);
        currentScreen = 9;
    }, LV_EVENT_CLICKED, NULL);

    lv_obj_t *swipe_hint = lv_label_create(scr_breath_hrv);
    lv_label_set_text(swipe_hint, "Swipe down to return");
    lv_obj_align(swipe_hint, LV_ALIGN_BOTTOM_MID, 0, -20);
    lv_obj_set_style_text_color(swipe_hint,
        lv_color_hex(0x666666), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(swipe_hint,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);
}

// ================================================================
//  ГРАФИК ЧД
// ================================================================
void createRespGraphScreen() {
    scr_resp_graph = lv_obj_create(NULL);
    lv_obj_set_style_bg_color(scr_resp_graph,
        lv_color_hex(0x1A1A2E), LV_STATE_DEFAULT);

    lv_obj_t *title = lv_label_create(scr_resp_graph);
    lv_label_set_text(title, "Respiratory Rate Today");
    lv_obj_align(title, LV_ALIGN_TOP_MID, 0, 30);
    lv_obj_set_style_text_color(title,
        lv_color_white(), LV_STATE_DEFAULT);

    resp_chart = lv_chart_create(scr_resp_graph);
    lv_obj_set_size(resp_chart, 180, 100);
    lv_obj_align(resp_chart, LV_ALIGN_CENTER, 10, -5);
    lv_chart_set_type(resp_chart, LV_CHART_TYPE_SCATTER);
    lv_chart_set_range(resp_chart,
        LV_CHART_AXIS_PRIMARY_Y, 5, 40);
    lv_chart_set_range(resp_chart,
        LV_CHART_AXIS_PRIMARY_X, 0, 23);
    lv_chart_set_point_count(resp_chart, 24);
    lv_obj_set_style_bg_color(resp_chart,
        lv_color_hex(0x1A1A2E), LV_PART_MAIN);
    lv_obj_set_style_bg_opa(resp_chart, 255, LV_PART_MAIN);
    lv_obj_set_style_line_color(resp_chart,
        lv_color_hex(0x333333), LV_PART_MAIN);
    lv_obj_set_style_border_width(resp_chart, 0, LV_PART_MAIN);

    // Серия создаётся ОДИН РАЗ
    resp_series = lv_chart_add_series(
        resp_chart,
        lv_color_hex(0x00E5FF),
        LV_CHART_AXIS_PRIMARY_Y
    );

    // Инициализируем все 24 точки как NONE
    for (int h = 0; h < 24; h++) {
        lv_chart_set_value_by_id2(
            resp_chart, resp_series,
            h, h, LV_CHART_POINT_NONE
        );
    }
    lv_chart_refresh(resp_chart);

    // Подписи оси X
    resp_x_label_0 = lv_label_create(scr_resp_graph);
    lv_label_set_text(resp_x_label_0, "0");
    lv_obj_align_to(resp_x_label_0, resp_chart,
        LV_ALIGN_BOTTOM_LEFT, -5, 25);
    lv_obj_set_style_text_color(resp_x_label_0,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(resp_x_label_0,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    resp_x_label_6 = lv_label_create(scr_resp_graph);
    lv_label_set_text(resp_x_label_6, "6");
    lv_obj_align_to(resp_x_label_6, resp_chart,
        LV_ALIGN_BOTTOM_MID, -40, 25);
    lv_obj_set_style_text_color(resp_x_label_6,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(resp_x_label_6,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    resp_x_label_12 = lv_label_create(scr_resp_graph);
    lv_label_set_text(resp_x_label_12, "12");
    lv_obj_align_to(resp_x_label_12, resp_chart,
        LV_ALIGN_BOTTOM_MID, 0, 25);
    lv_obj_set_style_text_color(resp_x_label_12,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(resp_x_label_12,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    resp_x_label_18 = lv_label_create(scr_resp_graph);
    lv_label_set_text(resp_x_label_18, "18");
    lv_obj_align_to(resp_x_label_18, resp_chart,
        LV_ALIGN_BOTTOM_RIGHT, -35, 25);
    lv_obj_set_style_text_color(resp_x_label_18,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(resp_x_label_18,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    // Подписи оси Y
    resp_y_label_min = lv_label_create(scr_resp_graph);
    lv_label_set_text(resp_y_label_min, "");
    lv_obj_align_to(resp_y_label_min, resp_chart,
        LV_ALIGN_BOTTOM_LEFT, -27, 10);
    lv_obj_set_style_text_color(resp_y_label_min,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(resp_y_label_min,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    resp_y_label_max = lv_label_create(scr_resp_graph);
    lv_label_set_text(resp_y_label_max, "");
    lv_obj_align_to(resp_y_label_max, resp_chart,
        LV_ALIGN_TOP_LEFT, -27, -8);
    lv_obj_set_style_text_color(resp_y_label_max,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(resp_y_label_max,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    // Подпись диапазона
    resp_range_label = lv_label_create(scr_resp_graph);
    lv_label_set_text(resp_range_label, "-- - -- brpm");
    lv_obj_align(resp_range_label, LV_ALIGN_BOTTOM_MID, 0, -35);
    lv_obj_set_style_text_color(resp_range_label,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);

    lv_obj_t *hint = lv_label_create(scr_resp_graph);
    lv_label_set_text(hint, "Swipe down to return");
    lv_obj_align(hint, LV_ALIGN_BOTTOM_MID, 0, -20);
    lv_obj_set_style_text_color(hint,
        lv_color_hex(0x666666), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(hint,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);
}

// ================================================================
//  ГРАФИК ВСР
// ================================================================
void createHRVGraphScreen() {
    scr_hrv_graph = lv_obj_create(NULL);
    lv_obj_set_style_bg_color(scr_hrv_graph,
        lv_color_hex(0x1A1A2E), LV_STATE_DEFAULT);

    lv_obj_t *title = lv_label_create(scr_hrv_graph);
    lv_label_set_text(title, "HRV (RMSSD) Today");
    lv_obj_align(title, LV_ALIGN_TOP_MID, 0, 20);
    lv_obj_set_style_text_color(title,
        lv_color_white(), LV_STATE_DEFAULT);

    hrv_chart = lv_chart_create(scr_hrv_graph);
    lv_obj_set_size(hrv_chart, 180, 100);
    lv_obj_align(hrv_chart, LV_ALIGN_CENTER, 10, -10);
    lv_chart_set_type(hrv_chart, LV_CHART_TYPE_SCATTER);
    lv_chart_set_range(hrv_chart,
        LV_CHART_AXIS_PRIMARY_Y, 0, 150);
    lv_chart_set_range(hrv_chart,
        LV_CHART_AXIS_PRIMARY_X, 0, 23);
    lv_chart_set_point_count(hrv_chart, 24);
    lv_obj_set_style_bg_color(hrv_chart,
        lv_color_hex(0x1A1A2E), LV_PART_MAIN);
    lv_obj_set_style_bg_opa(hrv_chart, 255, LV_PART_MAIN);
    lv_obj_set_style_line_color(hrv_chart,
        lv_color_hex(0x333333), LV_PART_MAIN);
    lv_obj_set_style_border_width(hrv_chart, 0, LV_PART_MAIN);

    // Серия создаётся ОДИН РАЗ
    hrv_series = lv_chart_add_series(
        hrv_chart,
        lv_color_hex(0xFFB300),
        LV_CHART_AXIS_PRIMARY_Y
    );

    // Инициализируем все 24 точки как NONE
    for (int h = 0; h < 24; h++) {
        lv_chart_set_value_by_id2(
            hrv_chart, hrv_series,
            h, h, LV_CHART_POINT_NONE
        );
    }
    lv_chart_refresh(hrv_chart);

    // Подписи оси X
    hrv_x_label_0 = lv_label_create(scr_hrv_graph);
    lv_label_set_text(hrv_x_label_0, "0");
    lv_obj_align_to(hrv_x_label_0, hrv_chart,
        LV_ALIGN_BOTTOM_LEFT, -5, 25);
    lv_obj_set_style_text_color(hrv_x_label_0,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(hrv_x_label_0,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    hrv_x_label_6 = lv_label_create(scr_hrv_graph);
    lv_label_set_text(hrv_x_label_6, "6");
    lv_obj_align_to(hrv_x_label_6, hrv_chart,
        LV_ALIGN_BOTTOM_MID, -40, 25);
    lv_obj_set_style_text_color(hrv_x_label_6,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(hrv_x_label_6,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    hrv_x_label_12 = lv_label_create(scr_hrv_graph);
    lv_label_set_text(hrv_x_label_12, "12");
    lv_obj_align_to(hrv_x_label_12, hrv_chart,
        LV_ALIGN_BOTTOM_MID, 0, 25);
    lv_obj_set_style_text_color(hrv_x_label_12,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(hrv_x_label_12,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    hrv_x_label_18 = lv_label_create(scr_hrv_graph);
    lv_label_set_text(hrv_x_label_18, "18");
    lv_obj_align_to(hrv_x_label_18, hrv_chart,
        LV_ALIGN_BOTTOM_RIGHT, -35, 25);
    lv_obj_set_style_text_color(hrv_x_label_18,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(hrv_x_label_18,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    // Подписи оси Y
    hrv_y_label_min = lv_label_create(scr_hrv_graph);
    lv_label_set_text(hrv_y_label_min, "");
    lv_obj_align_to(hrv_y_label_min, hrv_chart,
        LV_ALIGN_BOTTOM_LEFT, -27, 10);
    lv_obj_set_style_text_color(hrv_y_label_min,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(hrv_y_label_min,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    hrv_y_label_max = lv_label_create(scr_hrv_graph);
    lv_label_set_text(hrv_y_label_max, "");
    lv_obj_align_to(hrv_y_label_max, hrv_chart,
        LV_ALIGN_TOP_LEFT, -27, -8);
    lv_obj_set_style_text_color(hrv_y_label_max,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(hrv_y_label_max,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);

    // Подпись диапазона
    hrv_range_label = lv_label_create(scr_hrv_graph);
    lv_label_set_text(hrv_range_label, "-- - -- ms");
    lv_obj_align(hrv_range_label, LV_ALIGN_BOTTOM_MID, 0, -35);
    lv_obj_set_style_text_color(hrv_range_label,
        lv_color_hex(0xAAAAAA), LV_STATE_DEFAULT);

    lv_obj_t *hint = lv_label_create(scr_hrv_graph);
    lv_label_set_text(hint, "Swipe down to return");
    lv_obj_align(hint, LV_ALIGN_BOTTOM_MID, 0, -20);
    lv_obj_set_style_text_color(hint,
        lv_color_hex(0x666666), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(hint,
        &lv_font_montserrat_12, LV_STATE_DEFAULT);
}

// ================================================================
//  БУДИЛЬНИКИ
// ================================================================
void createAlarmListScreen() {
    scr_alarm_list = lv_obj_create(NULL);
    lv_obj_set_style_bg_color(scr_alarm_list,
        lv_color_hex(0x1A1A2E), LV_STATE_DEFAULT);
    lv_obj_set_style_pad_all(scr_alarm_list, 0, LV_STATE_DEFAULT);

    // Заголовок — создаётся один раз, никогда не пересоздаётся
    lv_obj_t *title = lv_label_create(scr_alarm_list);
    lv_label_set_text(title, "Alarms");
    lv_obj_align(title, LV_ALIGN_TOP_MID, 0, 10);
    lv_obj_set_style_text_color(title,
        lv_color_white(), LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(title,
        &lv_font_montserrat_14, LV_STATE_DEFAULT);

    // Фиксированные строки для каждого слота будильника
    for (int i = 0; i < MAX_ALARMS; i++) {

        // Контейнер строки
        alarm_rows[i] = lv_obj_create(scr_alarm_list);
        lv_obj_set_size(alarm_rows[i], 200, 40);
        lv_obj_align(alarm_rows[i], LV_ALIGN_TOP_MID,
            0, 35 + i * 45);
        lv_obj_set_style_bg_color(alarm_rows[i],
            lv_color_hex(0x333333), LV_STATE_DEFAULT);
        lv_obj_set_style_bg_opa(alarm_rows[i],
            255, LV_STATE_DEFAULT);
        lv_obj_set_style_border_width(alarm_rows[i],
            0, LV_STATE_DEFAULT);
        lv_obj_set_style_radius(alarm_rows[i],
            8, LV_STATE_DEFAULT);
        lv_obj_set_style_pad_all(alarm_rows[i],
            0, LV_STATE_DEFAULT);
        // Отключаем скролл внутри строки
        lv_obj_clear_flag(alarm_rows[i], LV_OBJ_FLAG_SCROLLABLE);

        // Метка времени — текст меняется в updateAlarmList()
        alarm_time_labels[i] = lv_label_create(alarm_rows[i]);
        lv_label_set_text(alarm_time_labels[i], "--:--");
        lv_obj_align(alarm_time_labels[i],
            LV_ALIGN_LEFT_MID, 45, 0);
        lv_obj_set_style_text_color(alarm_time_labels[i],
            lv_color_white(), LV_STATE_DEFAULT);
        lv_obj_set_style_text_font(alarm_time_labels[i],
            &lv_font_montserrat_18, LV_STATE_DEFAULT);

        // Переключатель вкл/выкл
        alarm_switches[i] = lv_switch_create(alarm_rows[i]);
        lv_obj_align(alarm_switches[i],
            LV_ALIGN_RIGHT_MID, -10, 0);
        lv_obj_add_event_cb(alarm_switches[i],
            alarmSwitchHandler,
            LV_EVENT_VALUE_CHANGED,
            (void*)(uintptr_t)i);

        // Кнопка удаления
        alarm_del_btns[i] = lv_btn_create(alarm_rows[i]);
        lv_obj_set_size(alarm_del_btns[i], 30, 30);
        lv_obj_align(alarm_del_btns[i],
            LV_ALIGN_LEFT_MID, 5, 0);
        lv_obj_set_style_bg_color(alarm_del_btns[i],
            lv_color_hex(0xFF3D00), LV_STATE_DEFAULT);
        lv_obj_set_style_radius(alarm_del_btns[i],
            4, LV_STATE_DEFAULT);
        lv_obj_t *del_label = lv_label_create(alarm_del_btns[i]);
        lv_label_set_text(del_label, "X");
        lv_obj_center(del_label);
        lv_obj_set_style_text_color(del_label,
            lv_color_white(), LV_STATE_DEFAULT);
        lv_obj_set_style_text_font(del_label,
            &lv_font_montserrat_12, LV_STATE_DEFAULT);
        lv_obj_add_event_cb(alarm_del_btns[i],
            btnDelAlarmHandler,
            LV_EVENT_CLICKED,
            (void*)(uintptr_t)i);

        // Все строки скрыты по умолчанию
        lv_obj_add_flag(alarm_rows[i], LV_OBJ_FLAG_HIDDEN);
    }

    // Кнопка добавления — создаётся один раз
    btn_add_alarm = lv_btn_create(scr_alarm_list);
    lv_obj_align(btn_add_alarm, LV_ALIGN_BOTTOM_MID, 0, -10);
    lv_obj_set_style_bg_color(btn_add_alarm,
        lv_color_hex(0x00AA55), LV_STATE_DEFAULT);
    lv_obj_t *label_add = lv_label_create(btn_add_alarm);
    lv_label_set_text(label_add, "Add alarm");
    lv_obj_set_style_text_color(label_add,
        lv_color_white(), LV_STATE_DEFAULT);
    lv_obj_center(label_add);
    lv_obj_add_event_cb(btn_add_alarm,
        btnAddAlarmHandler, LV_EVENT_CLICKED, NULL);
}

void updateAlarmList() {
    for (int i = 0; i < MAX_ALARMS; i++) {

        // Защита от невалидных указателей
        if (!alarm_rows[i]        ||
            !alarm_time_labels[i] ||
            !alarm_switches[i]    ||
            !alarm_del_btns[i])   continue;

        bool slotUsed = (alarms[i].enabled  ||
                         alarms[i].hour   != 0 ||
                         alarms[i].minute != 0);

        if (slotUsed) {
            // Показываем строку
            lv_obj_clear_flag(alarm_rows[i], LV_OBJ_FLAG_HIDDEN);

            // Обновляем текст времени
            char buf[8];
            sprintf(buf, "%02d:%02d",
                alarms[i].hour, alarms[i].minute);
            lv_label_set_text(alarm_time_labels[i], buf);

            // Обновляем состояние переключателя
            // Временно снимаем обработчик чтобы не
            // сработал alarmSwitchHandler при программном
            // изменении состояния
            lv_obj_remove_event_cb(alarm_switches[i],
                alarmSwitchHandler);

            if (alarms[i].enabled) {
                lv_obj_add_state(alarm_switches[i],
                    LV_STATE_CHECKED);
            } else {
                lv_obj_clear_state(alarm_switches[i],
                    LV_STATE_CHECKED);
            }

            // Возвращаем обработчик
            lv_obj_add_event_cb(alarm_switches[i],
                alarmSwitchHandler,
                LV_EVENT_VALUE_CHANGED,
                (void*)(uintptr_t)i);

        } else {
            // Скрываем строку — ноль аллокаций
            lv_obj_add_flag(alarm_rows[i], LV_OBJ_FLAG_HIDDEN);
        }
    }
}

void createAlarmSetScreen() {
    scr_alarm_set = lv_obj_create(NULL);
    lv_obj_set_style_bg_color(scr_alarm_set,
        lv_color_hex(0x1A1A2E), LV_STATE_DEFAULT);

    lv_obj_t *title = lv_label_create(scr_alarm_set);
    lv_label_set_text(title, "Set alarm");
    lv_obj_align(title, LV_ALIGN_TOP_MID, 0, 10);
    lv_obj_set_style_text_color(title,
        lv_color_white(), LV_STATE_DEFAULT);

    roller_hour = lv_roller_create(scr_alarm_set);
    lv_roller_set_options(roller_hour,
        "00\n01\n02\n03\n04\n05\n06\n07\n08\n09\n"
        "10\n11\n12\n13\n14\n15\n16\n17\n18\n19\n"
        "20\n21\n22\n23",
        LV_ROLLER_MODE_NORMAL);
    lv_roller_set_visible_row_count(roller_hour, 3);
    lv_obj_set_width(roller_hour, 70);
    lv_obj_align(roller_hour, LV_ALIGN_LEFT_MID, 25, 0);
    lv_obj_set_style_text_color(roller_hour,
        lv_color_white(), LV_PART_SELECTED);
    lv_obj_set_style_bg_color(roller_hour,
        lv_color_hex(0x333333), LV_PART_MAIN);
    lv_obj_set_style_bg_opa(roller_hour, 255, LV_PART_MAIN);
    lv_obj_set_style_border_width(roller_hour, 0, LV_PART_MAIN);

    roller_min = lv_roller_create(scr_alarm_set);
    lv_roller_set_options(roller_min,
        "00\n01\n02\n03\n04\n05\n06\n07\n08\n09\n"
        "10\n11\n12\n13\n14\n15\n16\n17\n18\n19\n"
        "20\n21\n22\n23\n24\n25\n26\n27\n28\n29\n"
        "30\n31\n32\n33\n34\n35\n36\n37\n38\n39\n"
        "40\n41\n42\n43\n44\n45\n46\n47\n48\n49\n"
        "50\n51\n52\n53\n54\n55\n56\n57\n58\n59",
        LV_ROLLER_MODE_NORMAL);
    lv_roller_set_visible_row_count(roller_min, 3);
    lv_obj_set_width(roller_min, 70);
    lv_obj_align(roller_min, LV_ALIGN_RIGHT_MID, -25, 0);
    lv_obj_set_style_text_color(roller_min,
        lv_color_white(), LV_PART_SELECTED);
    lv_obj_set_style_bg_color(roller_min,
        lv_color_hex(0x333333), LV_PART_MAIN);
    lv_obj_set_style_bg_opa(roller_min, 255, LV_PART_MAIN);
    lv_obj_set_style_border_width(roller_min, 0, LV_PART_MAIN);

    lv_obj_t *colon = lv_label_create(scr_alarm_set);
    lv_label_set_text(colon, ":");
    lv_obj_align(colon, LV_ALIGN_CENTER, 0, 0);
    lv_obj_set_style_text_font(colon,
        &lv_font_montserrat_48, LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(colon,
        lv_color_white(), LV_STATE_DEFAULT);

    label_alarm_time = lv_label_create(scr_alarm_set);
    lv_label_set_text(label_alarm_time, "00:00");
    lv_obj_align(label_alarm_time, LV_ALIGN_CENTER, 0, 60);
    lv_obj_set_style_text_font(label_alarm_time,
        &lv_font_montserrat_20, LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(label_alarm_time,
        lv_color_white(), LV_STATE_DEFAULT);

    lv_obj_add_event_cb(roller_hour, [](lv_event_t *e) {
        char buf[3];
        lv_roller_get_selected_str(roller_hour, buf, sizeof(buf));
        editHour = atoi(buf);
        char ts[6];
        sprintf(ts, "%02d:%02d", editHour, editMinute);
        lv_label_set_text(label_alarm_time, ts);
    }, LV_EVENT_VALUE_CHANGED, NULL);

    lv_obj_add_event_cb(roller_min, [](lv_event_t *e) {
        char buf[3];
        lv_roller_get_selected_str(roller_min, buf, sizeof(buf));
        editMinute = atoi(buf);
        char ts[6];
        sprintf(ts, "%02d:%02d", editHour, editMinute);
        lv_label_set_text(label_alarm_time, ts);
    }, LV_EVENT_VALUE_CHANGED, NULL);

    lv_obj_t *btn_set = lv_btn_create(scr_alarm_set);
    lv_obj_align(btn_set, LV_ALIGN_BOTTOM_MID, 0, -10);
    lv_obj_t *lbl_set = lv_label_create(btn_set);
    lv_label_set_text(lbl_set, "Set");
    lv_obj_add_event_cb(btn_set,
        btnSetAlarmHandler, LV_EVENT_CLICKED, NULL);
}

void createAlarmRingScreen() {
    scr_alarm_ring = lv_obj_create(NULL);
    lv_obj_set_style_bg_color(scr_alarm_ring,
        lv_color_hex(0x1A1A2E), LV_STATE_DEFAULT);

    lv_obj_t *title = lv_label_create(scr_alarm_ring);
    lv_label_set_text(title, "ALARM!");
    lv_obj_align(title, LV_ALIGN_TOP_MID, 0, 40);
    lv_obj_set_style_text_font(title,
        &lv_font_montserrat_48, LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(title,
        lv_color_hex(0xFF3D00), LV_STATE_DEFAULT);

    btn_stop_alarm = lv_btn_create(scr_alarm_ring);
    lv_obj_set_size(btn_stop_alarm, 130, 60);
    lv_obj_align(btn_stop_alarm, LV_ALIGN_CENTER, 0, 30);
    lv_obj_set_style_bg_color(btn_stop_alarm,
        lv_color_hex(0xFF3D00), LV_STATE_DEFAULT);
    lv_obj_t *btn_label = lv_label_create(btn_stop_alarm);
    lv_label_set_text(btn_label, "Stop");
    lv_obj_center(btn_label);

    lv_obj_add_event_cb(btn_stop_alarm, [](lv_event_t *e) {
        if (ringingAlarmIndex >= 0 &&
            ringingAlarmIndex < MAX_ALARMS)
        {
            alarms[ringingAlarmIndex].enabled = false;
            ringingAlarmIndex = -1;
        }
        digitalWrite(VIBRATION_MOTOR_PIN, LOW);
        vibrationActive = false;
        alarmActive     = false;
        lv_scr_load(scr_main);
        currentScreen = 0;
        saveBackup();
    }, LV_EVENT_CLICKED, NULL);
}

// ================================================================
//  ОБНОВЛЕНИЕ ГРАФИКА ПУЛЬСА
// ================================================================
void updateHRChart() {
    // Защита от невалидных указателей
    if (!hr_chart || !hr_series) return;

    // Сбрасываем все точки в NONE перед заполнением
    for (int h = 0; h < 24; h++) {
        lv_chart_set_value_by_id2(
            hr_chart, hr_series,
            h, h, LV_CHART_POINT_NONE
        );
    }

    if (!SD.exists("hr_log.txt")) {
        lv_chart_set_range(hr_chart,
            LV_CHART_AXIS_PRIMARY_Y, 40, 200);
        lv_label_set_text(y_label_min, "");
        lv_label_set_text(y_label_max, "");
        lv_label_set_text(hr_range_label, "-- - -- bpm");
        lv_chart_refresh(hr_chart);
        return;
    }

    int hourSum[24]   = {0};
    int hourCount[24] = {0};
    int absMin        = 999;
    int absMax        = 0;

    DateTime now    = rtc.now();
    int today_y     = now.year();
    int today_m     = now.month();
    int today_d     = now.day();

    File f = SD.open("hr_log.txt", FILE_READ);
    if (!f) return;

    // Статический буфер
    static char line[80];

    while (f.available()) {
        uint8_t len = 0;
        while (f.available() && len < sizeof(line) - 1) {
            char c = (char)f.read();
            if (c == '\n' || c == '\r') break;
            line[len++] = c;
        }
        line[len] = '\0';
        if (len == 0) continue;

        feedWDT();

        int y, mo, d, h, mi, s, bpm, sp;
        int parsed = sscanf(line,
            "%d-%d-%d %d:%d:%d,%d,%d",
            &y, &mo, &d, &h, &mi, &s, &bpm, &sp);
        if (parsed < 7) {
            parsed = sscanf(line,
                "%d-%d-%d %d:%d:%d,%d",
                &y, &mo, &d, &h, &mi, &s, &bpm);
        }

        if (parsed >= 7           &&
            y  == today_y         &&
            mo == today_m         &&
            d  == today_d         &&
            h  >= 0 && h  < 24   &&
            bpm >= 40 && bpm <= 200)
        {
            hourSum[h]   += bpm;
            hourCount[h] += 1;
            if (bpm < absMin) absMin = bpm;
            if (bpm > absMax) absMax = bpm;
        }
    }
    f.close();

    // Заполняем точки по индексу
    bool dataExists = false;
    for (int h = 0; h < 24; h++) {
        if (hourCount[h] > 0) {
            lv_chart_set_value_by_id2(
                hr_chart, hr_series,
                h,
                h,
                hourSum[h] / hourCount[h]
            );
            dataExists = true;
        }
    }

    // Обновляем подписи и диапазон
    if (dataExists) {
        todayMinBPM = absMin;
        todayMaxBPM = absMax;
        lv_chart_set_range(hr_chart,
            LV_CHART_AXIS_PRIMARY_Y, absMin, absMax);
        char buf[16];
        sprintf(buf, "%d", absMin);
        lv_label_set_text(y_label_min, buf);
        sprintf(buf, "%d", absMax);
        lv_label_set_text(y_label_max, buf);
        sprintf(buf, "%d - %d bpm", absMin, absMax);
        lv_label_set_text(hr_range_label, buf);
    } else {
        todayMinBPM = 999;
        todayMaxBPM = 0;
        lv_chart_set_range(hr_chart,
            LV_CHART_AXIS_PRIMARY_Y, 40, 200);
        lv_label_set_text(y_label_min, "");
        lv_label_set_text(y_label_max, "");
        lv_label_set_text(hr_range_label, "-- - -- bpm");
    }

    // Один вызов refresh в самом конце
    lv_chart_refresh(hr_chart);
}

// ================================================================
//  ОБНОВЛЕНИЕ ГРАФИКА ЧД
// ================================================================
void updateRespGraph() {
    // Защита от невалидных указателей
    if (!resp_chart || !resp_series) return;

    // Сбрасываем все точки в NONE перед заполнением
    for (int h = 0; h < 24; h++) {
        lv_chart_set_value_by_id2(
            resp_chart, resp_series,
            h, h, LV_CHART_POINT_NONE
        );
    }

    if (!SD.exists("resp_hrv_log.txt")) {
        lv_chart_set_range(resp_chart,
            LV_CHART_AXIS_PRIMARY_Y, 5, 40);
        lv_label_set_text(resp_y_label_min, "");
        lv_label_set_text(resp_y_label_max, "");
        lv_label_set_text(resp_range_label, "-- - -- brpm");
        lv_chart_refresh(resp_chart);
        return;
    }

    int hourSum[24]   = {0};
    int hourCount[24] = {0};
    int absMin        = 999;
    int absMax        = 0;

    DateTime now     = rtc.now();
    int      today_y = now.year();
    int      today_m = now.month();
    int      today_d = now.day();

    File f = SD.open("resp_hrv_log.txt", FILE_READ);
    if (!f) return;

    // Статический буфер
    static char line[80];

    while (f.available()) {
        uint8_t len = 0;
        while (f.available() && len < sizeof(line) - 1) {
            char c = (char)f.read();
            if (c == '\n' || c == '\r') break;
            line[len++] = c;
        }
        line[len] = '\0';
        if (len == 0) continue;

        feedWDT();

        int y, mo, d, h, mi, s, resp, hrv;
        int parsed = sscanf(line,
            "%d-%d-%d %d:%d:%d,%d,%d",
            &y, &mo, &d, &h, &mi, &s, &resp, &hrv);

        if (parsed >= 7           &&
            y  == today_y         &&
            mo == today_m         &&
            d  == today_d         &&
            h  >= 0 && h  < 24   &&
            resp >= 5 && resp <= 40)
        {
            hourSum[h]   += resp;
            hourCount[h] += 1;
            if (resp < absMin) absMin = resp;
            if (resp > absMax) absMax = resp;
        }
    }
    f.close();

    // Заполняем точки по индексу
    bool dataExists = false;
    for (int h = 0; h < 24; h++) {
        if (hourCount[h] > 0) {
            lv_chart_set_value_by_id2(
                resp_chart, resp_series,
                h,
                h,
                hourSum[h] / hourCount[h]
            );
            dataExists = true;
        }
    }

    // Обновляем подписи и диапазон
    if (dataExists) {
        int yMin = max(5,  absMin - 2);
        int yMax = min(40, absMax + 2);
        lv_chart_set_range(resp_chart,
            LV_CHART_AXIS_PRIMARY_Y, yMin, yMax);
        char buf[16];
        sprintf(buf, "%d", yMin);
        lv_label_set_text(resp_y_label_min, buf);
        sprintf(buf, "%d", yMax);
        lv_label_set_text(resp_y_label_max, buf);
        sprintf(buf, "%d - %d brpm", absMin, absMax);
        lv_label_set_text(resp_range_label, buf);
    } else {
        lv_chart_set_range(resp_chart,
            LV_CHART_AXIS_PRIMARY_Y, 5, 40);
        lv_label_set_text(resp_y_label_min, "");
        lv_label_set_text(resp_y_label_max, "");
        lv_label_set_text(resp_range_label, "-- - -- brpm");
    }

    lv_chart_refresh(resp_chart);
}

// ================================================================
//  ОБНОВЛЕНИЕ ГРАФИКА ВСР
// ================================================================
void updateHRVGraph() {
    // Защита от невалидных указателей
    if (!hrv_chart || !hrv_series) return;

    // Сбрасываем все точки в NONE перед заполнением
    for (int h = 0; h < 24; h++) {
        lv_chart_set_value_by_id2(
            hrv_chart, hrv_series,
            h, h, LV_CHART_POINT_NONE
        );
    }

    if (!SD.exists("resp_hrv_log.txt")) {
        lv_chart_set_range(hrv_chart,
            LV_CHART_AXIS_PRIMARY_Y, 0, 150);
        lv_label_set_text(hrv_y_label_min, "");
        lv_label_set_text(hrv_y_label_max, "");
        lv_label_set_text(hrv_range_label, "-- - -- ms");
        lv_chart_refresh(hrv_chart);
        return;
    }

    int hourSum[24]   = {0};
    int hourCount[24] = {0};
    int absMin        = 99999;
    int absMax        = 0;

    DateTime now     = rtc.now();
    int      today_y = now.year();
    int      today_m = now.month();
    int      today_d = now.day();

    File f = SD.open("resp_hrv_log.txt", FILE_READ);
    if (!f) return;

    // Статический буфер
    static char line[80];

    while (f.available()) {
        uint8_t len = 0;
        while (f.available() && len < sizeof(line) - 1) {
            char c = (char)f.read();
            if (c == '\n' || c == '\r') break;
            line[len++] = c;
        }
        line[len] = '\0';
        if (len == 0) continue;

        feedWDT();

        int y, mo, d, h, mi, s, resp, hrv;
        int parsed = sscanf(line,
            "%d-%d-%d %d:%d:%d,%d,%d",
            &y, &mo, &d, &h, &mi, &s, &resp, &hrv);

        if (parsed >= 8           &&
            y  == today_y         &&
            mo == today_m         &&
            d  == today_d         &&
            h  >= 0 && h  < 24   &&
            hrv >= 5 && hrv <= 300)
        {
            hourSum[h]   += hrv;
            hourCount[h] += 1;
            if (hrv < absMin) absMin = hrv;
            if (hrv > absMax) absMax = hrv;
        }
    }
    f.close();

    // Заполняем точки по индексу
    bool dataExists = false;
    for (int h = 0; h < 24; h++) {
        if (hourCount[h] > 0) {
            lv_chart_set_value_by_id2(
                hrv_chart, hrv_series,
                h,
                h,
                hourSum[h] / hourCount[h]
            );
            dataExists = true;
        }
    }

    // Обновляем подписи и диапазон
    if (dataExists) {
        int yMin = max(0,   absMin - 5);
        int yMax = min(300, absMax + 5);
        lv_chart_set_range(hrv_chart,
            LV_CHART_AXIS_PRIMARY_Y, yMin, yMax);
        char buf[16];
        sprintf(buf, "%d", yMin);
        lv_label_set_text(hrv_y_label_min, buf);
        sprintf(buf, "%d", yMax);
        lv_label_set_text(hrv_y_label_max, buf);
        sprintf(buf, "%d - %d ms", absMin, absMax);
        lv_label_set_text(hrv_range_label, buf);
    } else {
        lv_chart_set_range(hrv_chart,
            LV_CHART_AXIS_PRIMARY_Y, 0, 150);
        lv_label_set_text(hrv_y_label_min, "");
        lv_label_set_text(hrv_y_label_max, "");
        lv_label_set_text(hrv_range_label, "-- - -- ms");
    }

    lv_chart_refresh(hrv_chart);
}

// ================================================================
//  ОБРАБОТЧИКИ СОБЫТИЙ
// ================================================================
static void alarmSwitchHandler(lv_event_t *e) {
    lv_obj_t *sw    = lv_event_get_target(e);
    int       index = (int)(uintptr_t)lv_event_get_user_data(e);
    if (index < 0 || index >= MAX_ALARMS) return; // защита
    alarms[index].enabled = lv_obj_has_state(sw, LV_STATE_CHECKED);
    saveBackup();
}

static void btnAddAlarmHandler(lv_event_t *e) {
    DateTime now = rtc.now();
    editHour     = now.hour();
    editMinute   = now.minute();
    lv_roller_set_selected(roller_hour, editHour,   LV_ANIM_OFF);
    lv_roller_set_selected(roller_min,  editMinute, LV_ANIM_OFF);
    char ts[6];
    sprintf(ts, "%02d:%02d", editHour, editMinute);
    lv_label_set_text(label_alarm_time, ts);
    lv_scr_load(scr_alarm_set);
    currentScreen = 4;
}

static void btnSetAlarmHandler(lv_event_t *e) {
    // Ищем свободный слот
    int slot = -1;
    for (int i = 0; i < MAX_ALARMS; i++) {
        if (!alarms[i].enabled &&
            alarms[i].hour   == 0 &&
            alarms[i].minute == 0)
        {
            slot = i;
            break;
        }
    }

    if (slot == -1) {
        // Все слоты заняты — показываем предупреждение
        if (label_alarm_time) {
            lv_label_set_text(label_alarm_time, "Full!");
        }
        return;
    }

    alarms[slot].hour    = (uint8_t)editHour;
    alarms[slot].minute  = (uint8_t)editMinute;
    alarms[slot].enabled = true;

    updateAlarmList();
    lv_scr_load(scr_alarm_list);
    currentScreen = 3;
    saveBackup();
}

static void btnDelAlarmHandler(lv_event_t *e) {
    int index = (int)(uintptr_t)lv_event_get_user_data(e);
    if (index < 0 || index >= MAX_ALARMS) return; 

    alarms[index].enabled = false;
    alarms[index].hour    = 0;
    alarms[index].minute  = 0;

    updateAlarmList(); 
    saveBackup();
}

// ================================================================
//  ЖЕСТЫ
// ================================================================
static void swipeEventHandler(lv_event_t *e) {
    if (currentScreen == 5) return;
    if (lv_event_get_code(e) != LV_EVENT_GESTURE) return;
    lv_dir_t dir = lv_indev_get_gesture_dir(lv_indev_get_act());

    if (dir == LV_DIR_BOTTOM && currentScreen == 1) {
        updateHRChart(); lv_scr_load(scr_hr_log);
        currentScreen = 6; return;
    }
    if (dir == LV_DIR_TOP && currentScreen == 6) {
        lv_scr_load(scr_heart); currentScreen = 1; return;
    }
    if (dir == LV_DIR_BOTTOM && currentScreen == 7) {
        lv_scr_load(scr_heart); currentScreen = 1; return;
    }
    if (dir == LV_DIR_BOTTOM &&
        (currentScreen == 8 || currentScreen == 9)) {
        lv_scr_load(scr_breath_hrv); currentScreen = 7; return;
    }
    if (dir == LV_DIR_TOP && currentScreen == 0) {
        updateAlarmList(); lv_scr_load(scr_alarm_list);
        currentScreen = 3; return;
    }
    if (dir == LV_DIR_BOTTOM && currentScreen == 3) {
        lv_scr_load(scr_main); currentScreen = 0; return;
    }
    if (dir == LV_DIR_BOTTOM && currentScreen == 4) {
        lv_scr_load(scr_alarm_list); currentScreen = 3; return;
    }
    if (dir == LV_DIR_TOP && currentScreen == 1) {
        updateBreathHRVScreen();
        lv_scr_load(scr_breath_hrv); currentScreen = 7; return;
    }
    if (dir == LV_DIR_LEFT || dir == LV_DIR_RIGHT) {
        if (currentScreen == 0) {
            lv_scr_load(scr_heart); currentScreen = 1;
        } else if (currentScreen == 1) {
            lv_scr_load(scr_main);  currentScreen = 0;
        }
    }
}

// ================================================================
//  БУДИЛЬНИК
// ================================================================
void checkAlarm() {
    DateTime now = rtc.now();
    for (int i = 0; i < MAX_ALARMS; i++) {
        if (alarms[i].enabled &&
            alarms[i].hour   == now.hour() &&
            alarms[i].minute == now.minute() &&
            !vibrationActive && !alarmActive)
        {
            alarmActive        = true;
            ringingAlarmIndex  = i;
            lv_scr_load(scr_alarm_ring);
            currentScreen      = 5;
            digitalWrite(VIBRATION_MOTOR_PIN, HIGH);
            vibrationActive    = true;
            vibrationStartTime = millis();
            alarmRingStartTime = millis();
            return;
        }
    }
}

void handleVibration() {
    if (!vibrationActive) return;
    if (millis() - alarmRingStartTime >= alarmRingDuration) {
        digitalWrite(VIBRATION_MOTOR_PIN, LOW);
        vibrationActive = false;
        alarmActive     = false;
        lv_scr_load(scr_main);
        currentScreen = 0;
    }
}

// ================================================================
//  ШАГОМЕР
// ================================================================
void readIMU() {
    if (!imu_initialized) return;
    rawAccX = myIMU.readFloatAccelX();
    rawAccY = myIMU.readFloatAccelY();
    rawAccZ = myIMU.readFloatAccelZ();
    accX_f  = accX_f * (1.0f - FILTER_COEF) + rawAccX * FILTER_COEF;
    accY_f  = accY_f * (1.0f - FILTER_COEF) + rawAccY * FILTER_COEF;
    accZ_f  = accZ_f * (1.0f - FILTER_COEF) + rawAccZ * FILTER_COEF;
    gyroX   = myIMU.readFloatGyroX();
    gyroY   = myIMU.readFloatGyroY();
    gyroZ   = myIMU.readFloatGyroZ();
}

void updateStepCounter() {
    static unsigned long lastIMURead = 0;
    if (millis() - lastIMURead < 10) return;
    lastIMURead = millis();

    readIMU();

    float rawMag = sqrtf(
        rawAccX*rawAccX + rawAccY*rawAccY + rawAccZ*rawAccZ);
    accMagFiltered = accMagFiltered * 0.7f + rawMag * 0.3f;
    baseline       = baseline * 0.995f + rawMag * 0.005f;

    float threshold = baseline + STEP_DELTA;
    float gyroMag   = sqrtf(
        gyroX*gyroX + gyroY*gyroY + gyroZ*gyroZ);

    if (!peakDetected &&
        accMagFiltered > threshold && gyroMag < GYRO_LIMIT) {
        peakDetected = true;
    } else if (peakDetected &&
               accMagFiltered < (threshold - HYSTERESIS)) {
        peakDetected = false;
        if (millis() - lastStepTime > MIN_STEP_INTERVAL) {
            stepCount++;
            lastStepTime = millis();
        }
    }
}

// ================================================================
//  ОБНОВЛЕНИЕ UI
// ================================================================
void updateUIValues() {
    DateTime now = rtc.now();
    char tbuf[10], dbuf[12];
    sprintf(tbuf, "%02d:%02d", now.hour(), now.minute());
    sprintf(dbuf, "%02d.%02d", now.day(), now.month());
    lv_label_set_text(label_time, tbuf);
    lv_label_set_text(label_date, dbuf);

    char bbuf[10];
    sprintf(bbuf, "%d%%", batteryLevelPercent());
    lv_label_set_text(label_battery, bbuf);

    if (hrValue > 0) {
        char hbuf[20];
        sprintf(hbuf, "%d bpm", hrValue);
        lv_label_set_text(label_last_hr, hbuf);
    } else {
        lv_label_set_text(label_last_hr, "-- bpm");
    }

    char sbuf[20];
    sprintf(sbuf, "%d steps", stepCount);
    lv_label_set_text(label_steps, sbuf);

    bool found = false;
    for (int i = 0; i < MAX_ALARMS; i++) {
        if (alarms[i].enabled) {
            char abuf[20];
            sprintf(abuf, "%02d:%02d",
                alarms[i].hour, alarms[i].minute);
            lv_label_set_text(label_alarm, abuf);
            found = true;
            break;
        }
    }
    if (!found) lv_label_set_text(label_alarm, "Alarm off");

    if (currentScreen == 7) updateBreathHRVScreen();
}

bool isFingerOnSensor() {
    if (!sensor_initialized) return false;
    uint32_t ir  = particleSensor.getIR();
    uint32_t red = particleSensor.getRed();
    return (ir > 60000 && red > 50000);
}

void updateBreathHRVScreen() {
    if (!label_resp_rate || !label_hrv_value) return;

    char buf[16];

    if (hasDisplayResp) {
        sprintf(buf, "%d brpm", displayRespRate);
        lv_label_set_text(label_resp_rate, buf);
    } else {
        lv_label_set_text(label_resp_rate, "-- brpm");
    }

    if (hasDisplayHRV) {
        sprintf(buf, "%d ms", displayHRVValue);
        lv_label_set_text(label_hrv_value, buf);
    } else {
        lv_label_set_text(label_hrv_value, "-- ms");
    }
}

void updateHRDisplay() {
    if (autoMeasurementInProgress) return;

    if (hrValue >= 40 && hrValue <= 200) {
        char hbuf[16];
        sprintf(hbuf, "%d bpm", hrValue);
        lv_label_set_text(label_hr_value, hbuf);
        lv_color_t c =
            (hrValue < 60)   ? lv_color_hex(0x00E5FF) :
            (hrValue <= 100) ? lv_color_hex(0x00FF88) :
            (hrValue <= 140) ? lv_color_hex(0xFFB300) :
                               lv_color_hex(0xFF3D00);
        lv_obj_set_style_text_color(label_hr_value, c,
            LV_STATE_DEFAULT);
    }

    if (spo2Value >= 70 && spo2Value <= 100) {
        char sbuf[16];
        sprintf(sbuf, "%d%%", spo2Value);
        lv_label_set_text(label_spo2, sbuf);
        lv_color_t c =
            (spo2Value >= 95) ? lv_color_hex(0x00FF88) :
            (spo2Value >= 90) ? lv_color_hex(0xFFB300) :
                                lv_color_hex(0xFF3D00);
        lv_obj_set_style_text_color(label_spo2, c,
            LV_STATE_DEFAULT);
    }
}

// ================================================================
//  СБРОС СОСТОЯНИЯ ИЗМЕРЕНИЯ
// ================================================================
void resetMeasurementState() {
    irFiltered     = 0.0f;
    redFiltered    = 0.0f;
    hrAvg          = 0;
    lastHR         = 0;
    bufferIndex    = 0;
    slidingBufHead = 0;
    slidingBufFull = false;
    lastCalcTime   = 0;
    lastHRLogTime  = 0;
    sampleCount    = 0;
    prevIR         = 0;
    prevRed        = 0;
}

// ================================================================
//  КНОПКА "MEASURE"
// ================================================================
static void btnMeasureHandler(lv_event_t *e) {
    if (isMeasuring) return;
    if (!sensor_initialized) return;

    sensorWakeUp();
    delay(200);

    resetMeasurementState();

    displayRespRate = 0;
    displayHRVValue = 0;
    hasDisplayResp  = false;
    hasDisplayHRV   = false;

    lv_label_set_text(label_hr_value, "-- bpm");
    lv_label_set_text(label_spo2,     "-- %");
    lv_label_set_text(label_status,   "Hold finger...");
    lv_bar_set_value(bar, 0, LV_ANIM_OFF);
    lv_obj_add_flag(btn_measure, LV_OBJ_FLAG_HIDDEN);
    lv_obj_set_style_text_color(label_hr_value,
        lv_color_white(), LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(label_spo2,
        lv_color_white(), LV_STATE_DEFAULT);

    respRate = 0; hrvValue = 0;
    if (label_resp_rate)
        lv_label_set_text(label_resp_rate, "-- brpm");
    if (label_hrv_value)
        lv_label_set_text(label_hrv_value, "-- ms");

    autoMeasurementInProgress = false;
    isMeasuring               = true;
    measurementStart          = millis();
}

// ================================================================
//  ЗАПИСЬ ПУЛЬСА В SD
// ================================================================
void logHRToSD() {
    if (hrValue < 40 || hrValue > 200) return;
    if (millis() - lastHRLogTime < HR_LOG_INTERVAL_MS) return;
    lastHRLogTime = millis();

    feedWDT();

    DateTime now = rtc.now();
    char buf[64];
    sprintf(buf, "%04d-%02d-%02d %02d:%02d:%02d,%d,%d",
        now.year(), now.month(), now.day(),
        now.hour(), now.minute(), now.second(),
        hrValue, spo2Value);
    File f = SD.open("hr_log.txt", FILE_WRITE);
    if (f) { f.println(buf); f.close(); }
    feedWDT();
}

// ================================================================
//  ЗАПИСЬ ЧД/ВСР В SD
// ================================================================
void logRespHRVToSD() {
    if (!hasValidResp && !hasValidHRV) return;
    if (millis() - lastRespHRVLogTime < RESP_HRV_LOG_INTERVAL_MS)
        return;
    lastRespHRVLogTime = millis();

    feedWDT();

    DateTime now = rtc.now();
    char buf[64];
    sprintf(buf, "%04d-%02d-%02d %02d:%02d:%02d,%d,%d",
        now.year(), now.month(), now.day(),
        now.hour(), now.minute(), now.second(),
        hasValidResp ? respRate : -1,
        hasValidHRV  ? hrvValue : -1);
    File f = SD.open("resp_hrv_log.txt", FILE_WRITE);
    if (f) { f.println(buf); f.close(); }
    feedWDT();
}

// ================================================================
//  РАСЧЁТ ЧД И ВСР
// ================================================================
void calcRespAndHRV() {
    unsigned long t0 = millis();
    Serial.print("DBG calcRespAndHRV start, samples=");
    Serial.println(sampleCount);

    int tail = slidingBufHead;
    for (int i = 0; i < SLIDING_WINDOW_SIZE; i++) {
        linearBuf[i] =
            slidingIrBuf[(tail + i) % SLIDING_WINDOW_SIZE];
    }

    float newResp = computeRespiratoryRate(
        linearBuf, SENSOR_FS, SLIDING_WINDOW_SIZE);

    if (newResp >= 5.0f && newResp <= 40.0f) {
        respRate        = (int)newResp;
        hasValidResp    = true;
        // Обновляем display-значения только при успехе
        displayRespRate = respRate;
        hasDisplayResp  = true;
    }

    int localPeaks[MAX_PEAKS];
    int peakCnt = findPeaks(
        linearBuf, SLIDING_WINDOW_SIZE,
        localPeaks, SENSOR_FS / 3, MAX_PEAKS);

    if (peakCnt >= 3) {
        float newHRV = computeHRV(
            localPeaks, peakCnt, SENSOR_FS);
        if (newHRV >= 5.0f && newHRV <= 300.0f) {
            hrvValue        = (int)newHRV;
            hasValidHRV     = true;
            // Обновляем display-значения только при успехе
            displayHRVValue = hrvValue;
            hasDisplayHRV   = true;
        }
    }

    historyTimestamps[historyIndex] = millis();
    respHistory[historyIndex]       = (float)respRate;
    hrvHistory[historyIndex]        = (float)hrvValue;
    historyIndex = (historyIndex + 1) % MAX_HISTORY;

    respGraphNeedsUpdate = true;
    hrvGraphNeedsUpdate  = true;

    if (currentScreen == 7) updateBreathHRVScreen();

    logRespHRVToSD();

    Serial.print("Samples: "); Serial.print(sampleCount);
    Serial.print(" | Resp: "); Serial.print(respRate);
    Serial.print(" brpm | HRV: "); Serial.print(hrvValue);
    Serial.print(" ms | calc_ms: ");
    Serial.println(millis() - t0);
}

// ================================================================
//  ОСНОВНОЙ ЦИКЛ ИЗМЕРЕНИЯ
// ================================================================
void updateMeasurement() {
    if (!isMeasuring)        return;
    if (!sensor_initialized) return;

    unsigned long now = millis();
    if (now - lastSampleTime < SENSOR_PERIOD_MS) return;

    uint32_t irValue, redValue;
    if (!readSensor(irValue, redValue)) {
        if (!sensor_initialized) stopMeasurement(false);
        return;
    }

    prevIR  = irValue;
    prevRed = redValue;

    lastSampleTime = now;
    sampleCount++;

    if (autoMeasurementInProgress &&
        sampleCount >= AUTO_MAX_SAMPLES)
    {
        Serial.print("Auto measurement complete: ");
        Serial.print(sampleCount);
        Serial.println(" samples");
        stopMeasurement(true);
        return;
    }

    if (irValue < 60000 || redValue < 50000) {
        if (now - measurementStart > 2000UL) {
            stopMeasurement(false);
        }
        return;
    }

    measurementStart = now;

    const float alpha = 0.75f;
    irFiltered  = alpha * irFiltered
                + (1.0f - alpha) * (float)irValue;
    redFiltered = alpha * redFiltered
                + (1.0f - alpha) * (float)redValue;

    irBuffer[bufferIndex]  = (uint32_t)irFiltered;
    redBuffer[bufferIndex] = (uint32_t)redFiltered;
    bufferIndex++;

    slidingIrBuf[slidingBufHead] = (uint32_t)irFiltered;
    slidingBufHead = (slidingBufHead + 1) % SLIDING_WINDOW_SIZE;
    if (slidingBufHead == 0) slidingBufFull = true;

    if (!autoMeasurementInProgress) {
        if (!slidingBufFull) {
            int progress = (int)((sampleCount * 100UL)
                / SLIDING_WINDOW_SIZE);
            lv_bar_set_value(bar,
                constrain(progress, 0, 100), LV_ANIM_OFF);
        } else {
            lv_bar_set_value(bar, 0, LV_ANIM_OFF);
        }
    }

    if (bufferIndex >= BUFFER_SIZE) {
        maxim_heart_rate_and_oxygen_saturation(
            irBuffer,  BUFFER_SIZE,
            redBuffer,
            &n_spo2,   &spo2_valid,
            &n_heart_rate, &hr_valid);

        if (hr_valid &&
            n_heart_rate >= 40 &&
            n_heart_rate <= 200)
        {
            if (lastHR == 0 ||
                abs(n_heart_rate - lastHR) < 20)
            {
                int weight = constrain(
                    (int)(sampleCount / BUFFER_SIZE), 1, 8);
                hrAvg = (hrAvg == 0)
                    ? n_heart_rate
                    : (hrAvg * weight + n_heart_rate)
                      / (weight + 1);
                lastHR  = hrAvg;
                hrValue = lastHR;
            }
        }

        if (spo2_valid && n_spo2 >= 70 && n_spo2 <= 100) {
            spo2Value = (int)n_spo2;
        }

        int half = BUFFER_SIZE / 2;
        for (int i = 0; i < half; i++) {
            irBuffer[i]  = irBuffer[i + half];
            redBuffer[i] = redBuffer[i + half];
        }
        bufferIndex = half;

        if (!autoMeasurementInProgress) {
            if (sampleCount <=
                (unsigned long)(BUFFER_SIZE * 2))
            {
                lv_bar_set_value(bar, 0, LV_ANIM_OFF);
                lv_label_set_text(label_status, "Measuring...");
            }
            updateHRDisplay();
        }

        logHRToSD();
    }

    if (slidingBufFull &&
        (millis() - lastCalcTime) >= CALC_INTERVAL_MS)
    {
        lastCalcTime = millis();
        calcRespAndHRV();

        if (!autoMeasurementInProgress) {
            stopMeasurement(true);
        }
    }
}

// ================================================================
//  ЗАВЕРШЕНИЕ ИЗМЕРЕНИЯ
// ================================================================
void stopMeasurement(bool success) {
    isMeasuring = false;
    sensorSleep();

    lastAutoMeasureTime = millis();

    if (!autoMeasurementInProgress) {
        lv_bar_set_value(bar, 0, LV_ANIM_OFF);
        lv_obj_clear_flag(btn_measure, LV_OBJ_FLAG_HIDDEN);

        if (!success) {
            lv_label_set_text(label_hr_value, "Finger off");
            lv_obj_set_style_text_color(label_hr_value,
                lv_color_white(), LV_STATE_DEFAULT);
            lv_label_set_text(label_spo2, "");
            lv_obj_set_style_text_color(label_spo2,
                lv_color_white(), LV_STATE_DEFAULT);
            lv_label_set_text(label_status, "");
        } else {
            lv_label_set_text(label_status, "");
        }
    }

    if (!success) {
        hrValue      = 0;
        spo2Value    = 0;
        // Сбрасываем рабочие флаги, но НЕ display-значения
        respRate     = 0;
        hrvValue     = 0;
        hasValidResp = false;
        hasValidHRV  = false;
    }

    autoMeasurementInProgress = false;
    resetMeasurementState();
}

// ================================================================
//  АЛГОРИТМЫ СИГНАЛА
// ================================================================
int findPeaks(uint32_t *buffer, int length,
              int *peaks, int minDistance, int maxPeaks)
{
    int count = 0;
    for (int i = 1; i < length - 1 && count < maxPeaks; i++) {
        if (buffer[i] > buffer[i-1] &&
            buffer[i] > buffer[i+1])
        {
            if (count == 0 ||
                (i - peaks[count-1]) >= minDistance)
                peaks[count++] = i;
        }
    }
    return count;
}

int findPeaksFloat(float *buffer, int length,
                   int *peaks, int minDistance, int maxPeaks)
{
    int count = 0;
    for (int i = 1; i < length - 1 && count < maxPeaks; i++) {
        if (buffer[i] > buffer[i-1] &&
            buffer[i] > buffer[i+1])
        {
            if (count == 0 ||
                (i - peaks[count-1]) >= minDistance)
                peaks[count++] = i;
        }
    }
    return count;
}

float computeRespiratoryRate(uint32_t *buf, int fs, int length) {
    float dcMean = 0.0f;
    for (int i = 0; i < length; i++)
        dcMean += (float)buf[i];
    dcMean /= (float)length;

    for (int i = 0; i < length; i++)
        ac_buf[i] = (float)buf[i] - dcMean;

    const int envWindow = fs / 2;

    float slidingSum = 0.0f;
    int   initEnd    = min(envWindow, length - 1);
    for (int j = 0; j <= initEnd; j++)
        slidingSum += ac_buf[j] * ac_buf[j];

    for (int i = 0; i < length; i++) {
        int addIdx = i + envWindow;
        if (addIdx < length)
            slidingSum += ac_buf[addIdx] * ac_buf[addIdx];

        int remIdx = i - envWindow - 1;
        if (remIdx >= 0)
            slidingSum -= ac_buf[remIdx] * ac_buf[remIdx];

        int cnt = min(i + envWindow, length - 1)
                - max(0, i - envWindow) + 1;
        env_buf[i] = sqrtf(slidingSum / (float)cnt);
    }

    int respPeaks[50];
    int pCnt = findPeaksFloat(env_buf, length,
        respPeaks, (int)(fs * 1.5f), 50);
    if (pCnt < 2) return 0.0f;

    float avgInterval = 0.0f;
    for (int i = 1; i < pCnt; i++)
        avgInterval += (float)(respPeaks[i] - respPeaks[i-1]);
    avgInterval /= (float)(pCnt - 1);
    if (avgInterval <= 0.0f) return 0.0f;

    return constrain(
        60.0f * (float)fs / avgInterval, 5.0f, 40.0f);
}

float computeHRV(int *peaks, int peakCount, int fs) {
    if (peakCount < 3) return 0.0f;

    float rr[MAX_PEAKS];
    int   rrCount = 0;
    for (int i = 1; i < peakCount; i++) {
        float ms = (float)(peaks[i] - peaks[i-1])
                   / (float)fs * 1000.0f;
        if (ms >= 300.0f && ms <= 2000.0f)
            rr[rrCount++] = ms;
    }
    if (rrCount < 2) return 0.0f;

    float sumSqDiff = 0.0f;
    for (int i = 1; i < rrCount; i++) {
        float d = rr[i] - rr[i-1];
        sumSqDiff += d * d;
    }
    return constrain(
        sqrtf(sumSqDiff / (float)(rrCount - 1)),
        5.0f, 300.0f);
}

// ================================================================
//  ДАТЧИК — СОН / ПРОБУЖДЕНИЕ / БЕЗОПАСНОЕ ЧТЕНИЕ
// ================================================================
void sensorSleep() {
    if (!sensor_initialized) return;
    particleSensor.shutDown();
    Serial.println("Sensor sleeping");
}

void sensorWakeUp() {
    if (!sensor_initialized) {
        Serial.println("Sensor reinit...");
        recoverI2CBus();
        sensor_initialized = initSensor();
        if (!sensor_initialized) {
            Serial.println("Sensor reinit failed");
            return;
        }
        lastI2CCheck = millis();
        Serial.println("Sensor awake (reinit)");
        return;
    }

    particleSensor.wakeUp();
    delay(200);
    particleSensor.clearFIFO();
    lastI2CCheck = millis();
    Serial.println("Sensor awake");
}

bool recoverI2CBus() {
    pinMode(PIN_WIRE_SCL, OUTPUT);
    pinMode(PIN_WIRE_SDA, OUTPUT);

    for (int i = 0; i < 9; i++) {
        digitalWrite(PIN_WIRE_SCL, HIGH);
        delayMicroseconds(5);
        digitalWrite(PIN_WIRE_SCL, LOW);
        delayMicroseconds(5);
    }
    digitalWrite(PIN_WIRE_SDA, LOW);
    digitalWrite(PIN_WIRE_SCL, HIGH);
    delayMicroseconds(5);
    digitalWrite(PIN_WIRE_SDA, HIGH);
    delayMicroseconds(5);

    Wire.begin();
    Wire.setClock(400000);
    delay(50);
    return true;
}

bool initSensor() {
    Wire.beginTransmission(0x57);
    uint8_t err = Wire.endTransmission();
    if (err != 0) {
        Serial.print("MAX30102 I2C error: ");
        Serial.println(err);
        return false;
    }

    if (!particleSensor.begin(Wire, I2C_SPEED_FAST))
        return false;

    particleSensor.setup(0x1F, 1, 2, 100, 411, 4096);
    particleSensor.setPulseAmplitudeRed(0x1F);
    particleSensor.setPulseAmplitudeIR(0x1F);
    particleSensor.setPulseAmplitudeGreen(0);
    particleSensor.clearFIFO();

    prevIR  = 0;
    prevRed = 0;

    Serial.println("MAX30102 OK");
    return true;
}

bool readSensor(uint32_t &ir, uint32_t &red) {
    if (!sensor_initialized) return false;

    unsigned long now = millis();
    if (now - lastI2CCheck >= I2C_CHECK_INTERVAL) {
        lastI2CCheck = now;
        Wire.beginTransmission(0x57);
        uint8_t err = Wire.endTransmission();
        if (err != 0) {
            sensorErrorStreak++;
            Serial.print("I2C err=");
            Serial.println(err);
            if (sensorErrorStreak >= 3) {
                sensor_initialized = false;
                sensorErrorStreak  = 0;
            }
            return false;
        }
        sensorErrorStreak = 0;
    }

    ir  = particleSensor.getIR();
    red = particleSensor.getRed();

    if (ir == 0 && red == 0)            return false;
    if (ir == prevIR && red == prevRed) return false;

    return true;
}

// ================================================================
//  АВТОИЗМЕРЕНИЕ
// ================================================================
void autoMeasureHeartRate() {
    if (isMeasuring)         return;
    if (!sensor_initialized) return;
    if (millis() - lastAutoMeasureTime < AUTO_MEASURE_INTERVAL)
        return;

    sensorWakeUp();

    Wire.beginTransmission(0x57);
    if (Wire.endTransmission() != 0) {
        Serial.println("Sensor not ready at auto start");
        sensorSleep();
        lastAutoMeasureTime = millis();
        return;
    }

    delay(50);

    uint32_t ir  = particleSensor.getIR();
    uint32_t red = particleSensor.getRed();

    if (ir < 60000 || red < 50000) {
        sensorSleep();
        lastAutoMeasureTime = millis();
        return;
    }

    particleSensor.clearFIFO();
    delay(20);

    resetMeasurementState();
    lastI2CCheck              = millis();
    autoMeasurementInProgress = true;
    isMeasuring               = true;
    measurementStart          = millis();
    lastAutoMeasureTime       = millis();
    Serial.println("Auto measurement started");
}

// ================================================================
//  BACKUP
// ================================================================
void saveBackup() {
    if (!SD.begin(SD_CS_PIN)) return;

    SD.remove("backup.txt");
    File f = SD.open("backup.txt", FILE_WRITE);
    if (!f) return;

    DateTime now = rtc.now();

    feedWDT();

    f.printf("steps:%d %02d.%02d\n",
        stepCount, now.day(), now.month());

    for (int i = 0; i < MAX_ALARMS; i++) {
        f.printf("alarm:%d,%d,%d,%d\n",
            i, 
            alarms[i].hour, 
            alarms[i].minute,
            alarms[i].enabled ? 1 : 0);

        feedWDT();
    }
    f.close();
}

void loadBackup() {
    if (!SD.exists("backup.txt")) return;
    File f = SD.open("backup.txt", FILE_READ);
    if (!f) return;
    DateTime now        = rtc.now();
    int      todayDay   = now.day();
    int      todayMonth = now.month();

    while (f.available()) {
        String line = f.readStringUntil('\n');
        line.trim();
        int steps, d, m;
        feedWDT();
        if (sscanf(line.c_str(),
            "steps:%d %d.%d", &steps, &d, &m) == 3) {
            stepCount = (d == todayDay && m == todayMonth)
                ? steps : 0;
            continue;
        }
        if (sscanf(line.c_str(),
            "steps:%d", &steps) == 1) {
            stepCount = steps; continue;
        }
        int idx, h, mi, en;
        if (sscanf(line.c_str(),
            "alarm:%d,%d,%d,%d", &idx, &h, &mi, &en) == 4 &&
            idx >= 0 && idx < MAX_ALARMS)
        {
            alarms[idx].hour    = (uint8_t)h;
            alarms[idx].minute  = (uint8_t)mi;
            alarms[idx].enabled = (en == 1);
        }
    }
    f.close();
}

// ================================================================
//  СБРОС ПО СМЕНЕ ДНЯ
// ================================================================
void checkDayReset() {
    static unsigned long lastCheck = 0;
    if (millis() - lastCheck < 60000UL) return;
    lastCheck = millis();

    DateTime now        = rtc.now();
    int      currentDay = now.day();

    if (lastDay == -1) { lastDay = currentDay; return; }

    if (currentDay != lastDay) {
        stepCount = 0;
        lastDay   = currentDay;

        // Архивируем лог ЧД/ВСР при смене дня
        if (SD.exists("resp_hrv_log.txt")) {
            SD.remove("resp_hrv_log_prev.txt");
            File src = SD.open("resp_hrv_log.txt",     FILE_READ);
            File dst = SD.open("resp_hrv_log_prev.txt", FILE_WRITE);
            if (src && dst) {
                while (src.available())
                    dst.write(src.read());
            }
            if (src) src.close();
            if (dst) dst.close();
            feedWDT();
            SD.remove("resp_hrv_log.txt");
        }

        // Разрешаем немедленную запись в новый день
        lastRespHRVLogTime = 0;

        saveBackup();
        Serial.println("Day changed, steps + resp/hrv log reset");
    }
}

// ================================================================
//  ДИСПЛЕЙ — ЖЕСТ ПОДНЯТИЯ РУКИ
// ================================================================
void handleGesture() {
    float mag = sqrtf(
        accX_f*accX_f + accY_f*accY_f + accZ_f*accZ_f);
    static unsigned long lastMotion = 0;
    if (mag > 1.5f) {
        lastMotion = millis();
        if (!displayOn) {
            displayOn = true;
            digitalWrite(D6, HIGH);
        }
    }
    if (millis() - lastMotion > 10000UL && displayOn) {
        displayOn = false;
        digitalWrite(D6, LOW);
    }
}

// ================================================================
//  БАТАРЕЯ
// ================================================================
int batteryLevelPercent() {
    static int           cachedPercent = 100;
    static unsigned long lastRead      = 0;

    if (millis() - lastRead < 30000UL)
        return cachedPercent;
    lastRead = millis();

    pinMode(VBAT_ENABLE, OUTPUT);
    digitalWrite(VBAT_ENABLE, LOW);
    delay(10);
    analogReadResolution(12);
    analogReference(AR_INTERNAL_1_2);
    int raw = analogRead(PIN_VBAT);
    digitalWrite(VBAT_ENABLE, HIGH);
    pinMode(VBAT_ENABLE, INPUT);

    float voltage = (float)raw * (1.2f / 4095.0f) * 6.0f * 2.96f;
    int   mvolts  = (int)(voltage * 1000.0f);

    if      (mvolts >= 4200) cachedPercent = 100;
    else if (mvolts <= 3200) cachedPercent = 89;
    else if (mvolts > 3800)
        cachedPercent = (int)map(mvolts, 3800, 4200, 50, 100);
    else if (mvolts > 3650)
        cachedPercent = (int)map(mvolts, 3650, 3800, 10, 50);
    else
        cachedPercent = (int)map(mvolts, 3200, 3650, 0,  10);

    return cachedPercent;
}

// ================================================================
//  WDT
// ================================================================
void armWDT() {
    NRF_WDT->TASKS_START = 1;
    wdt_armed     = true;
    last_wdt_feed = millis();
    Serial.println("WDT ARMED");
}

void feedWDT() {
    if (!wdt_armed) return;
    NRF_WDT->RR[0] = 0x6E524635;
    last_wdt_feed  = millis();
}

void markFunctionEntry() {
    function_entry_time = millis();
}

bool checkFunctionTimeout(const char *func_name) {
    unsigned long e = millis() - function_entry_time;
    if (e > FUNCTION_TIMEOUT_MS) {
        Serial.print("HANG in ");
        Serial.print(func_name);
        Serial.print(" (");
        Serial.print(e);
        Serial.println(" ms)");
        return true;
    }
    return false;
}

extern "C" void HardFault_Handler(void) {
    NVIC_SystemReset();
    while (1) {}
}