| benchmark | family | dim L/R | modes L/R | inv | needed | used (needed in bold) | used, not needed | time (s) | SYNC | lambda=1 file | NO_REPO | SINGLE_STEP (info) | uniform rows | diagnostics |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | ACC under sensor spoofing / retune | 2/2 | 1/1 | linear | S M | **S** **M** I | I | 0.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `acc_spoof_limp` | ACC under sensor spoofing / retune | 1/1 | 2/3 | linear | M B I X | **M** **B** **I** **X** | - | 0.1 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `acc_tune_lag` | ACC under sensor spoofing / retune | 2/2 | 1/1 | linear | S M | **S** **M** I | I | 0.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `acc_tune_limp` | ACC under sensor spoofing / retune | 1/1 | 2/2 | linear | S M D I | **S** **M** P **D** **I** | P | 0.6 | DECLINED | DECLINED | CERTIFIED | DECLINED | CRUISE:DECLINED, LIMP:CERTIFIED (drops a stated row) | S_lam1 D_rows |
| `antenna_track_kvretune` | Ground-station antenna (servo retune) | 3/3 | 3/3 | linear | D | **D** I | I | 0.9 | CERTIFIED | - | CERTIFIED | CERTIFIED | TRACK:DECLINED, STOW/STOWED:CERTIFIED (drops a stated row) | D_rows |
| `autoclave_liquid_steambank` | Steam sterilizer liquids cycle | 3/3 | 4/4 | linear | S R D | **S** **R** **D** I | I | 1.3 | DECLINED | DECLINED | DECLINED | CERTIFIED | HEAT/EQUIL:DECLINED, EXPOSE/EXHAUST:DECLINED (drops a stated row) | S_lam1 R_cover D_rows D_strict |
| `boiler_purge_vfd` | Steam boiler cold start (purge retrofit) | 3/3 | 2/2 | linear | R D | **R** **D** I | I | 0.2 | DECLINED | - | DECLINED | CERTIFIED | PURGE:DECLINED, FIRE:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `bottling_fill_strainer` | Bottle filler (clogged product strainer) | 2/2 | 2/2 | linear | S I | **S** **I** | - | 0.5 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | - | S_lam1 |
| `canal_gate_notches` | Irrigation canal gate notches | 1/1 | 3/4 | linear | X | I **X** | I | 0.3 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `elevator_start_discbrake` | Elevator trip | 3/3 | 4/4 | linear | R D | **R** **D** I | I | 1.0 | DECLINED | - | DECLINED | CERTIFIED | LIFT:DECLINED, UP/APP/STOP:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `engine_start_highidle` | Turbofan ground start | 3/3 | 6/6 | linear | R D I | **R** **D** **I** | - | 0.8 | DECLINED | - | DECLINED | CERTIFIED | STARTER/STARTER_LOW:DECLINED, LIGHTOFF/ABORT:DECLINED (drops a stated row), SELF/IDLE:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `extruder_pe100_manualstart` | Extruder start-up (manual speed steps) | 2/2 | 4/4 | linear | M B P I | **M** **B** **P** **I** | - | 0.8 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `flaps_slow_approach` | Airliner flap extension (one hydraulic system lost) | 2/2 | 2/2 | linear | S | **S** I | I | 0.2 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | - | S_lam1 |
| `furnace_program_timebase` | Heat-treatment furnace program | 2/2 | 3/3 | linear | S I | **S** **I** | - | 1.1 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | - | S_lam1 |
| `gantry_speed_zones` | Gantry speed zones (multi-cycle matching) | 2/2 | 3/1 | linear | S M | **S** **M** I | I | 1.2 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `h2_refuel_ambientbias` | Hydrogen refuelling (sensor bias) | 1/1 | 7/5 | linear | R D I | **R** **D** **I** | - | 0.8 | DECLINED | - | DECLINED | CERTIFIED | STAGE1/STAGE2/STAGE3/STAGE3DRAWN:DECLINED, TOPOFF/TOPOFFEARLY/COMPLETE:CERTIFIED (drops a stated row) | R_cover D_rows |
| `hydro_rejection_gatecal` | Hydro unit load rejection | 3/3 | 2/2 | linear | D | **D** I | I | 0.3 | CERTIFIED | - | CERTIFIED | CERTIFIED | ONGRID:DECLINED, REJECT:DECLINED (drops a stated row) | D_rows D_strict |
| `lit_csf21_vehicle_bus` | Literature | 3/3 | 6/12 | linear | X | I **X** | I | 3.5 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `lit_csf21_vehicle_thermo` | Literature | 3/3 | 6/6 | linear | X | I **X** | I | 1.8 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `lit_csf25_salt_tank_hold` | Literature | 2/2 | 2/2 | linear | S D I | **S** **D** **I** | - | 0.2 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | HoldInc:DECLINED (drops a stated row), HoldDec:DECLINED (drops a stated row), conj:DECLINED | S_lam1 D_rows D_strict |
| `lit_drl_lane_control` | Literature | 3/3 | 6/6 | linear | X | I **X** | I | 2.8 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `lit_freedm_meter` | Literature | 2/2 | 12/12 | linear | X | I **X** | I | 2.5 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `lit_girard08_robot` | Literature | 6/2 | 6/6 | quadratic | X | I **X** | I | 57.1 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `lit_gpt10_boost_converter` | Literature | 2/2 | 48/2 | quadratic | X | I **X** | I | 64.4 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `lit_lz21_vehicle_position` | Literature | 2/2 | 3/3 | linear | X | I **X** | I | 0.3 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `lit_nahs25_engine_cooling` | Literature | 1/1 | 2/2 | linear | R | **R** | - | 0.1 | DECLINED | - | DECLINED | CERTIFIED | - | R_cover |
| `lit_nahs25_salt_tank` | Literature | 1/1 | 2/2 | linear | S | **S** I | I | 0.1 | DECLINED | - | CERTIFIED | CERTIFIED | - | - |
| `molding_pack_checkring` | Injection molding pack and hold | 3/3 | 2/2 | linear | D | **D** I | I | 0.3 | CERTIFIED | - | CERTIFIED | CERTIFIED | HOLD:DECLINED, COOL:DECLINED (drops a stated row) | D_rows D_strict |
| `platoon_linkloss` | Platoon follower (CACC: link loss, latency, profiles) | 2/2 | 2/1 | linear | M | **M** I | I | 0.2 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `platoon_profiles` | Platoon follower (CACC: link loss, latency, profiles) | 2/2 | 1/1 | linear | S M | **S** **M** I | I | 0.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `quad_light_lag` | Quadrotor climb, lighter airframe | 3/3 | 1/1 | linear | S M | **S** **M** I | I | 0.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `quad_light_profiles` | Quadrotor climb, lighter airframe | 2/2 | 3/3 | linear | S M B X | **S** **M** **B** I **X** | I | 11.2 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `rampmeter_poll_2to1` | Freeway ramp metering (polled detectors) | 3/3 | 6/6 | linear | M B | **M** **B** P I | P I | 2.2 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `reactor_feed_wireless` | Exothermic reactor feed interlock | 2/2 | 4/4 | linear | M B P | **M** **B** **P** I | I | 0.7 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `rover_ladder_2to3` | Rover ladder | 3/3 | 3/3 | linear | -- | I | I | 0.2 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `rover_ladder_3to6` | Rover ladder | 6/6 | 3/3 | linear | -- | I | I | 0.8 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `rover_ladder_6to8` | Rover ladder | 8/8 | 3/3 | quadratic | S M I | **S** **M** **I** | - | 16.5 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `rover_ladder_8to12` | Rover ladder | 12/12 | 3/3 | quadratic | S M I | **S** **M** **I** | - | 34.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `rover_terrain_2to4` | Terrain chain | 4/4 | 3/3 | linear | I | **I** | - | 0.5 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `rover_terrain_4to6` | Terrain chain | 6/6 | 3/3 | linear | I | **I** | - | 1.1 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `sat3w_detumble_phases` | Rigid-body detumbling (polynomial) | 6/6 | 2/3 | quadratic | M I X | **M** P **I** **X** | P | 21.1 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `sat_detumble_phases` | Rigid-body detumbling (polynomial) | 4/4 | 2/3 | quadratic | M I X | **M** P **I** **X** | P | 7.5 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `sat_detumble_weak` | Rigid-body detumbling (polynomial) | 4/4 | 1/4 | quadratic | S M B X | **S** **M** **B** P I **X** | P I | 4.2 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `syringe_relay_prearm` | Syringe-pump relay | 4/4 | 6/4 | linear | R D | **R** **D** I | I | 1.2 | DECLINED | - | DECLINED | CERTIFIED | RUN1/PREARM/READY/TAKEUP2:DECLINED, RUN2/END:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `tank_dos_3to1` | Tank under sampling DoS | 2/2 | 4/4 | linear | M I | **M** **I** | - | 0.9 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `train_ato_odometry` | Train speed control (ATO) | 1/1 | 3/3 | linear | S M B | **S** **M** **B** I | I | 2.4 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | - | S_lam1 |
| `turbine_startup_gearratio` | Wind turbine start-up | 3/3 | 5/5 | linear | R D I X | **R** **D** **I** **X** | - | 1.0 | DECLINED | - | DECLINED | CERTIFIED | SPINUP/RAMP/GEN:DECLINED (drops a stated row), REG/GUST:CERTIFIED (drops a stated row), conj:DECLINED | R_cover D_rows |
| `ventilator_vc_cuffleak` | Volume-controlled ventilation | 2/2 | 2/2 | linear | D I | **D** **I** | - | 0.2 | CERTIFIED | - | CERTIFIED | CERTIFIED | INSP:DECLINED (drops a stated row), EXP:DECLINED (drops a stated row), conj:DECLINED | D_rows D_strict |
| `watertank` | Watertank | 1/1 | 3/5 | linear | S M B | **S** **M** **B** P I | P I | 2.2 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `watertank_twospeed` | Watertank | 1/1 | 3/6 | linear | S M B | **S** **M** **B** I | I | 2.0 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |

Totals (needed, the `letters` field and `\numletter<L>`): S 19, M 21, R 8, B 9, P 2, D 13, I 17, X 14

Totals (used, `\numletter<L>used`): S 19, M 21, R 8, B 9, P 8, D 13, I 49, X 14

Used and needed (2026-10-30): see the docstring of scripts/suite_v2_letters.py. Needed = the ablation rule (with the mechanism switched off the tool declines; M and B by the cover shape, so needed = used). Used = the mechanism appears in the certificate the tool produced (S a stretch other than 1, 0 included; M a multi-step cover; R a right-only node; B a joint step with >= 2 retained successors; P any pruned edge; D rows that differ per left mode; I a checked cut kept in the certificate; X a committed successor subset). No other screens (owner's decision 2026-10-30, replacing the batch-11 screens).

D rule (2026-10-27): the stated requirement differs per mode, so the claim needs mode-dependent rows: matrix M5 and every uniform row set from the file's own rows that keeps every stated requirement declines; a uniform row marked (drops a stated row) may certify without removing D. Under the earlier strict rule (every uniform row set declines, diagnostic D_strict) D = 9.
