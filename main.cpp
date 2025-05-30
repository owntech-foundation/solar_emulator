#include "DataAPI.h"
#include "TaskAPI.h"
#include "TwistAPI.h"
#include "SpinAPI.h"
#include "pid.h"
#include "zephyr/console/console.h"
#include <math.h>

//====================================================================
//                    Déclarations globales
//====================================================================

// Déclaration des tâches en boucle
void loop_application_task();   // Tâche principale : moyennes et logique d’application
void loop_communication_task(); // Tâche de communication série
void loop_critical_task();      // Tâche de lecture des capteurs et contrôle PWM

// Paramètres pour l'interpolation I–V 
#define HISTORY_SIZE 2  // Taille de l’historique pour garantir le régime permanent du courant
#define N_POINTS     11 // Nombre de points pour l’approximation de la courbe I–V

// Caractéristiques électriques du panneau
const float32_t Voc = 44; // Tension en circuit ouvert [V]
const float32_t Isc = 5.1f;  // Courant de court-circuit [A]
const float32_t Vm  = 35.8f; // Tension au point de puissance max [V]
const float32_t Im  = 4.61f; // Courant au point de puissance max [A]

// Structure représentant un segment linéaire de la courbe I–V
struct Segment {
    float32_t a;    // Pente du segment (dI/dV)
    float32_t b;    // Ordonnée à l’origine
    float32_t Vmin; // Tension minimale de validité
    float32_t Vmax; // Tension maximale de validité
};
Segment segments[N_POINTS - 1]; // Tableau des segments

// Variables globales 
static uint32_t controlTaskPeriod = 100; // Période de la tâche critique en µs
static bool     pwmEnable         = false;
uint8_t         receivedChar;          // Caractère reçu via série

// Valeurs mesurées
static float32_t lowVoltage1, lowVoltage2; // Tensions mesurées côté basse tension
static float32_t lowCurrent1, lowCurrent2; // Courants mesurés côté basse tension
static float32_t highCurrent, highVoltage; // Tension et courant mesurés côté haute tension
static float     measData;                // Valeur brute lue

// Variables de commande
float32_t dutyCycle             = 0.5f;  // Rapport cyclique initial
static float32_t dutyCycleP     = 0.5f;  // Rapport cyclique en mode POWER
static float32_t voltageReferenceP = 25.0f; // Référence tension en mode POWER
static float32_t voltageReferenceE = 25.0f; // Référence tension en mode EMULATOR

// Paramètres PID
static float32_t kp = 0.000215f;
static float32_t Ti = 7.5175e-5f;
static float32_t Td = 0.0f;
static float32_t Np = 0.0f;
static float32_t upperBound = 1.0f;
static float32_t lowerBound = 0.0f;
static float32_t Ts = controlTaskPeriod * 1e-6f; // Période PID [s]
static PidParams pidParams(Ts, kp, Ti, Td, Np, lowerBound, upperBound);
static Pid       pid;                         

// Modes de fonctionnement
enum modeMenu { MODE_IDLE = 0, MODE_POWER, MODE_EMULATOR };
uint8_t mode = MODE_IDLE;

// Accumulateurs pour calcul des moyennes 
static volatile float32_t sumLowCurrent1 = 0.0f, sumLowVoltage1 = 0.0f;
static volatile float32_t sumLowCurrent2 = 0.0f, sumLowVoltage2 = 0.0f;
static volatile float32_t sumHighCurrent = 0.0f, sumHighVoltage = 0.0f;
static volatile uint32_t  measurementCount = 0;

// Historique et flags pour EMULATOR MODE 
static float32_t currentHistory[HISTORY_SIZE] = {0.0f, 0.0f};
static bool      emulatorSteadyState     = false;
static bool      waitingSteadyState       = false;

// Dernier point stable (intersection)
static float32_t lastSteadyVoltage = 0.0f;
static float32_t lastSteadyCurrent = 0.0f;
static float32_t lastDutyCycle  = 0.0f;

// Compteur de détection de changement de charge
static uint32_t loadChangeCounter = 0;

// Seuils et persistance 
#define LOAD_RESISTANCE_THRESHOLD    0.02f // Variation relative de R > 2%
#define DUTY_CYCLE_CHANGE_THRESHOLD  0.05f // Variation du rapport cyclique > 0.05
#define CURRENT_STABILITY_THRESHOLD  0.45f // 0.45 A pour stabilité initiale
#define REQUIRED_PERSISTENCE_COUNT   2     // Nombre de cycles pour valider un événement


//====================================================================
//                  Fonctions utilitaires
//====================================================================

/**
 * updateHistory()
 *  
 * Met à jour un historique circulaire des deux dernières mesures.
*/
void updateHistory(float32_t *hist, float32_t val) {
    hist[0] = hist[1];
    hist[1] = val;
}

/**
 * computeVoltagePoints()
 *
 * Génère un tableau de tensions pour l'interpolation de la courbe I–V.
 * Les points sont répartis de 0 à Voc selon des fractions de Vm.
 */
void computeVoltagePoints(float32_t V[N_POINTS]) {
    V[0]  = 0.0f;
    V[1]  = 0.2f * Vm;
    V[2]  = 0.4f * Vm;
    V[3]  = 0.6f * Vm;
    V[4]  = 0.8f * Vm;
    V[5]  = 0.9f * Vm;
    V[6]  = Vm;
    V[7]  = (Vm + Voc) / 2.0f;
    V[8]  = 0.9f * Voc;
    V[9]  = 0.95f * Voc;
    V[10] = Voc;
}

/**
 * computeCParameter()
 *
 * Calcule le paramètre c de la loi exponentielle du panneau solaire.
 */
float32_t computeCParameter() {
    return -(Voc - Vm) / logf(1.0f - Im / Isc);
}

/**
 * computeCurrentPoints()
 *
 * Calcule les courants correspondant aux tensions pour la courbe I–V.
 * I[i] = Isc * (1 - exp((V[i] - Voc) / c)).
 */
void computeCurrentPoints(float32_t I[N_POINTS], float32_t V[N_POINTS], float32_t c) {
    for (int i = 0; i < N_POINTS; i++) {
        I[i] = Isc * (1.0f - expf((V[i] - Voc) / c));
    }
}

/**
 * computeSegments()
 *
 * Génère les segments linéaires (droites) pour approximer la courbe I–V.
 * Chaque segment couvre [Vmin, Vmax] avec pente a et intercept b.
 */
void computeSegments(Segment segments[N_POINTS-1], float32_t V[N_POINTS], float32_t I[N_POINTS]) {
    for (int i = 0; i < N_POINTS - 1; i++) {
        segments[i].a    = (I[i+1] - I[i]) / (V[i+1] - V[i]);
        segments[i].b    = I[i] - segments[i].a * V[i];
        segments[i].Vmin = V[i];
        segments[i].Vmax = V[i+1];
    }
}

/**
 * findIntersection()
 *
 * Recherche l'intersection entre la droite de charge et les segments I–V.
 */
void findIntersection(Segment segments[N_POINTS-1], int n,
                      float32_t Vmes, float32_t Imes,
                      float32_t &Vint, float32_t &Iint) {
    float32_t a_mes = (Vmes != 0.0f) ? (Imes / Vmes) : 0.0f;
    for (int i = 0; i < n; i++) {
        Vint = (0.0f - segments[i].b) / (segments[i].a - a_mes);
        Iint = a_mes * Vint;
        if (Vint >= segments[i].Vmin && Vint <= segments[i].Vmax) {
            return; // intersection valide
        }
    }
    Vint = Iint = -1.0f; // pas trouvé
}

//====================================================================
//               Configuration et initialisation
//====================================================================

/**
 * setup_routine()
 *
 * Initialise le matériel, les capteurs, le PID et crée les tâches.
 * - Configure les capteurs via DataAPI.
 * - Initialisation du PID avec les paramètres définis.
 * - Calcul des segments pour la courbe I–V.
 * - Création et lancement des tâches :
 *    • loop_application_task (background)
 *    • loop_communication_task (background)
 *    • loop_critical_task (critique, période controlTaskPeriod)
 */
void setup_routine() {
    // Initialisation hardware
    spin.version.setBoardVersion(SPIN_v_1_0);
    twist.setVersion(shield_TWIST_V1_3);
    twist.initAllBuck();

    // Configuration des capteurs
    data.enableTwistDefaultChannels();
    data.setParameters(V1_LOW, 0.0456f, -92.69f);
    data.setParameters(V2_LOW, 0.0453f, -92.061f);
    data.setParameters(V_HIGH, 0.0299f, 0.2921f);
    data.setParameters(I1_LOW, 0.0056f, -11.537f);
    data.setParameters(I2_LOW, 0.0046f, -9.3977f);
    data.setParameters(I_HIGH, 0.0046f, -9.1739f);

    // Initialisation du PID
    pid.init(pidParams);

    // Calcul des segments I–V
    float32_t Vp[N_POINTS], Ip[N_POINTS];
    computeVoltagePoints(Vp);
    float32_t c = computeCParameter();
    computeCurrentPoints(Ip, Vp, c);
    computeSegments(segments, Vp, Ip);

    // Création et démarrage des tâches
    uint8_t appTaskId  = task.createBackground(loop_application_task);
    uint8_t commTaskId = task.createBackground(loop_communication_task);
    task.createCritical(loop_critical_task, controlTaskPeriod);
    task.startBackground(appTaskId);
    task.startBackground(commTaskId);
    task.startCritical();

}

//====================================================================
//                  Boucle de communication série
//====================================================================

/**
 * loop_communication_task()
 *
 * Tâche en arrière-plan gérant l'interface série.
 * - Attend un caractère entré.
 * - Met à jour le mode de fonctionnement 
 */
void loop_communication_task() {
    while (1) {
        receivedChar = console_getchar();
        switch (receivedChar) {
        case 'h':
            // Affiche le menu
            printk(" ________________________________________\n");
            printk("|   ---- MENU mode tension buck ----     |\n");
            printk("|   appuyez sur i : mode idle             |\n");
            printk("|   appuyez sur p : mode power            |\n");
            printk("|   appuyez sur e : mode emulator         |\n");
            printk("|   appuyez sur u : augmenter la réf. tension\n");
            printk("|   appuyez sur d : diminuer la réf. tension\n");
            printk("||\n\n");
            break;
        case 'i':
            // Mode veille
            printk("mode idle\n");
            mode = MODE_IDLE;
            break;
        case 'p':
            // Mode Buck (POWER)
            printk("mode power\n");
            mode = MODE_POWER;
            dutyCycle = dutyCycleP;
            break;
        case 'e':
            // Mode émulateur
            printk("mode emulator\n");
            dutyCycleP = dutyCycle;
            mode           = MODE_EMULATOR;
            dutyCycle      = 0.9f;                
            twist.setAllDutyCycle(dutyCycle);
            currentHistory[0] = currentHistory[1] = 0.0f;
            emulatorSteadyState = false;
            waitingSteadyState   = false;
            loadChangeCounter       = 0;
            break;
        case 'u':
            // Augmente le rapport cyclique
            dutyCycle += 0.1f;
            break;
        case 'd':
            // Diminue le rapport cyclique
            dutyCycle -= 0.1f;
            break;
        default:
            break;
        }
    }
}

//====================================================================
//            Tâche principale d’application 
//====================================================================

/**
 * loop_application_task()
 *
 * Tâche de fond qui accumule les mesures et calcule la moyenne sur une période d'accumulation de 500 µs
 * 
 * En mode émulateur :
 * On vérifie la stabilité du courant et on calcule l’intersection entre la droite de charge et la caractéristique I–V 
 * pour déterminer la valeur de voltageReferenceE. Affichage du point de test, de l’équation de la droite de charge et 
 * du point d’intersection. On gère également le changement de charge dynamique en recalibrant le système et 
 * en recalculant le point d’intersection.
 */
void loop_application_task() {
    static uint32_t elapsed = 0;
    elapsed += 100;

    // Indicateur LED selon mode
    if (mode == MODE_IDLE) spin.led.turnOff(); else spin.led.turnOn();

    // Période de calcul des moyennes (en µs)
    uint32_t period = 500;
    if (elapsed >= period && measurementCount > 0) {
        // Calcul des moyennes
        float32_t avgLowI1 = sumLowCurrent1 / measurementCount;
        float32_t avgLowV1 = sumLowVoltage1 / measurementCount;
        float32_t avgLowI2 = sumLowCurrent2 / measurementCount;
        float32_t avgLowV2 = sumLowVoltage2 / measurementCount;
        float32_t avgHighI = sumHighCurrent   / measurementCount;
        float32_t avgHighV = sumHighVoltage   / measurementCount;
        float32_t avgI     = avgLowI1 + avgLowI2;
        float32_t avgV     = (avgLowV1 + avgLowV2) * 0.5f;

        printk("Moyennes (dernières %uµs) :\n", period);
        printk("lowCurrent1: %f\n", avgLowI1);
        printk("lowVoltage1: %f\n", avgLowV1);
        printk("lowCurrent2: %f\n", avgLowI2);
        printk("lowVoltage2: %f\n", avgLowV2);
        printk("highCurrent: %f\n", avgHighI);
        printk("highVoltage: %f\n", avgHighV);

        // Émulateur : charge statique
        if (mode == MODE_EMULATOR && !emulatorSteadyState) {
            updateHistory(currentHistory, avgI);
            if (fabsf(currentHistory[1] - currentHistory[0]) < CURRENT_STABILITY_THRESHOLD) {
                float32_t Vint, Iint;
                findIntersection(segments, N_POINTS - 1, avgV, currentHistory[1], Vint, Iint);
                voltageReferenceE = Vint;
                // Affichage : point de test, droite de charge, intersection
                printk("Point de test (dutyCycle = 0.9) : V_test = %f, I_test = %f\n", avgV, avgI);
                float32_t loadLineSlope = (avgV != 0.0F) ? (avgI / avgV) : 0.0F;
                printk("Equation de la droite de charge : I = %f * V\n", loadLineSlope);
                printk("Intersection trouvée : Vo* = %f, Io* = %f\n", Vint, Iint);
                lastSteadyVoltage = Vint;
                lastSteadyCurrent = Iint;
                emulatorSteadyState = true;
                loadChangeCounter = 0;
            } else {
                printk("Mesures instables pour la phase de mesure initiale.\n");
            }
        }

        // Émulateur : adaptation dynamique de la charge
        if (mode == MODE_EMULATOR && emulatorSteadyState) {
            float32_t candidateI = avgI;
            float32_t candidateV = avgV;
            float32_t currentDuty = dutyCycle;

            if (fabsf(currentDuty - lastDutyCycle) > DUTY_CYCLE_CHANGE_THRESHOLD) {
                waitingSteadyState = true;
                loadChangeCounter     = 0;
                lastSteadyVoltage   = candidateV;
                lastSteadyCurrent   = candidateI;
            }
            else if (waitingSteadyState) {
                if (fabsf(currentHistory[1] - currentHistory[0]) < CURRENT_STABILITY_THRESHOLD){
                    waitingSteadyState = false;
                    lastSteadyVoltage   = candidateV;
                    lastSteadyCurrent   = candidateI;
                }
            }
            else {
                float32_t Rlast = (lastSteadyCurrent > 0.0f) ? (lastSteadyVoltage / lastSteadyCurrent) : 0.0f;
                float32_t Rcand = (candidateI > 0.0f) ? (candidateV / candidateI) : 0.0f;
                float32_t relErr = (Rlast > 0.0f) ? fabsf(Rcand - Rlast) / Rlast : 0.0f;
                if (relErr > LOAD_RESISTANCE_THRESHOLD) {
                    loadChangeCounter++;
                    if (loadChangeCounter >= REQUIRED_PERSISTENCE_COUNT) {
                        loadChangeCounter = 0;
                        dutyCycle = 0.9f;
                        emulatorSteadyState = false;
                        twist.setAllDutyCycle(dutyCycle);
                        printk("Recalibration \n");
                    }
                } else {
                    loadChangeCounter = 0;
                    lastSteadyVoltage = candidateV;
                    lastSteadyCurrent = candidateI;
                }
            }
            lastDutyCycle = currentDuty;
        }

        // Réinitialisation des accumulateurs
        sumLowCurrent1 = sumLowVoltage1 = sumLowCurrent2 = sumLowVoltage2 =
        sumHighCurrent = sumHighVoltage = 0.0f;
        measurementCount = 0;
        elapsed = 0;
    }
    task.suspendBackgroundMs(100);
}

//====================================================================
//               Tâche critique (lecture + PWM)
//====================================================================

/**
 * loop_critical_task()
 *
 * Tâche temps-réel pour lire les capteurs et ajuster le PWM :
 * - Lecture des tensions et courants (low/high) via DataAPI.
 * - Sélection du comportement selon le mode :
 *    MODE_IDLE   : arrêt du PWM
 *    MODE_POWER  : régulation PID sur voltageReferenceP
 *    MODE_EMULATOR: maintien 0.9 jusqu'à mesure, puis PID sur voltageReferenceE
 * - Accumulation des mesures pour la tâche applicative.
 */
void loop_critical_task() {
    // Lecture des capteurs
    measData = data.getLatest(I1_LOW);   if (measData != NO_VALUE) lowCurrent1  = measData;
    measData = data.getLatest(V1_LOW);   if (measData != NO_VALUE) lowVoltage1  = measData;
    measData = data.getLatest(I2_LOW);   if (measData != NO_VALUE) lowCurrent2  = measData;
    measData = data.getLatest(V2_LOW);   if (measData != NO_VALUE) lowVoltage2  = measData;
    measData = data.getLatest(I_HIGH);   if (measData != NO_VALUE) highCurrent  = measData;
    measData = data.getLatest(V_HIGH);   if (measData != NO_VALUE) highVoltage  = measData;

    if (mode == MODE_IDLE) {
        // MODE_IDLE : on arrête simplement le PWM, pas d'accumulation
        if (pwmEnable) {
            twist.stopAll();
        }
        pwmEnable = false;
    }
    else if (mode == MODE_POWER) {
        // MODE_POWER : calcul PID, application et accumulation
        dutyCycle = pid.calculateWithReturn(voltageReferenceP, lowVoltage1);
        twist.setAllDutyCycle(dutyCycle);

        sumLowCurrent1 += lowCurrent1;
        sumLowVoltage1 += lowVoltage1;
        sumLowCurrent2 += lowCurrent2;
        sumLowVoltage2 += lowVoltage2;
        sumHighCurrent  += highCurrent;
        sumHighVoltage  += highVoltage;
        measurementCount++;

        if (!pwmEnable) {
            pwmEnable = true;
            twist.startAll();
        }
    }
    else { // MODE_EMULATOR
        // EMULATOR : 0.9f jusqu'à mesure initiale, puis régulation PID
        if (!emulatorSteadyState) {
            dutyCycle = 0.9f;
            twist.setAllDutyCycle(dutyCycle);
        } else {
            dutyCycle = pid.calculateWithReturn(voltageReferenceE, lowVoltage1);
            twist.setAllDutyCycle(dutyCycle);
        }

        sumLowCurrent1 += lowCurrent1;
        sumLowVoltage1 += lowVoltage1;
        sumLowCurrent2 += lowCurrent2;
        sumLowVoltage2 += lowVoltage2;
        sumHighCurrent  += highCurrent;
        sumHighVoltage  += highVoltage;
        measurementCount++;

        if (!pwmEnable) {
            pwmEnable = true;
            twist.startAll();
        }
    }
}
//====================================================================
//                        Point d'entrée
//====================================================================

/**
 * main()
 *
 * Point d'entrée du programme :
 * - Appelle setup_routine() pour initialiser le système.
 * - Boucle principale gérée par le scheduler Zephyr.
 */
int main(void) {
    setup_routine();
    return 0;
}
