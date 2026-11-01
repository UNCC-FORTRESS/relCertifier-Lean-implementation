| benchmark | family | dim L/R | modes L/R | inv | needed | used (needed in bold) | used, not needed | time (s) | SYNC | lambda=1 file | NO_REPO | SINGLE_STEP (info) | uniform rows | diagnostics |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | ACC under sensor spoofing / retune | 2/2 | 1/1 | linear | S | **S** M I | M I | 0.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `acc_spoof_limp` | ACC under sensor spoofing / retune | 1/1 | 2/3 | linear | I | M R B **I** | M R B | 0.1 | CERTIFIED | - | CERTIFIED | DECLINED | - | R_cover |
| `acc_tune_lag` | ACC under sensor spoofing / retune | 2/2 | 1/1 | linear | S | **S** M I | M I | 0.0 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `acc_tune_limp` | ACC under sensor spoofing / retune | 1/1 | 2/2 | linear | S D I | **S** M P **D** **I** | M P | 0.5 | DECLINED | DECLINED | CERTIFIED | DECLINED | CRUISE:DECLINED, LIMP:CERTIFIED (drops a stated row) | S_lam1 D_rows |
| `antenna_track_kvretune` | Ground-station antenna (servo retune) | 3/3 | 3/3 | linear | D | **D** I | I | 1.0 | CERTIFIED | - | CERTIFIED | CERTIFIED | TRACK:DECLINED, STOW/STOWED:CERTIFIED (drops a stated row) | D_rows |
| `autoclave_liquid_steambank` | Steam sterilizer liquids cycle | 3/3 | 4/4 | linear | S R D | **S** **R** **D** I | I | 1.4 | DECLINED | DECLINED | DECLINED | CERTIFIED | HEAT/EQUIL:DECLINED, EXPOSE/EXHAUST:DECLINED (drops a stated row) | S_lam1 R_cover D_rows D_strict |
| `boiler_purge_vfd` | Steam boiler cold start (purge retrofit) | 3/3 | 2/2 | linear | R D | **R** **D** I | I | 0.2 | DECLINED | - | DECLINED | CERTIFIED | PURGE:DECLINED, FIRE:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `bottling_fill_strainer` | Bottle filler (clogged product strainer) | 2/2 | 2/2 | linear | S I | **S** **I** | - | 0.5 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | - | S_lam1 |
| `canal_gate_notches` | Irrigation canal gate notches | 1/1 | 3/4 | linear | X | R I **X** | R I | 0.3 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | R_cover |
| `elevator_start_discbrake` | Elevator trip | 3/3 | 4/4 | linear | R | **R** D I | D I | 1.3 | DECLINED | - | DECLINED | CERTIFIED | LIFT:CERTIFIED, UP/APP/STOP:DECLINED (drops a stated row) | R_cover D_rows |
| `engine_start_highidle` | Turbofan ground start | 3/3 | 6/6 | linear | R D I | **R** **D** **I** | - | 1.0 | DECLINED | - | DECLINED | CERTIFIED | STARTER/STARTER_LOW:DECLINED, LIGHTOFF/ABORT:DECLINED (drops a stated row), SELF/IDLE:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `extruder_pe100_manualstart` | Extruder start-up (manual speed steps) | 2/2 | 4/4 | linear | P I | M B **P** **I** | M B | 7.9 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `flaps_slow_approach` | Airliner flap extension (one hydraulic system lost) | 2/2 | 2/2 | linear | S | **S** I | I | 0.2 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | - | S_lam1 |
| `furnace_program_timebase` | Heat-treatment furnace program | 2/2 | 3/3 | linear | S I | **S** **I** | - | 1.1 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | - | S_lam1 |
| `gantry_speed_zones` | Gantry speed zones (multi-cycle matching) | 2/2 | 3/1 | linear | S | **S** M I | M I | 1.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `h2_refuel_ambientbias` | Hydrogen refuelling (sensor bias) | 1/1 | 7/5 | linear | R D I | **R** **D** **I** | - | 0.7 | DECLINED | - | DECLINED | CERTIFIED | STAGE1/STAGE2/STAGE3/STAGE3DRAWN:DECLINED, TOPOFF/TOPOFFEARLY/COMPLETE:CERTIFIED (drops a stated row) | R_cover D_rows |
| `hydro_rejection_gatecal` | Hydro unit load rejection | 3/3 | 2/2 | linear | D | **D** I | I | 0.3 | CERTIFIED | - | CERTIFIED | CERTIFIED | ONGRID:DECLINED, REJECT:DECLINED (drops a stated row) | D_rows D_strict |
| `lit_csf21_vehicle_bus` | Literature | 3/3 | 6/12 | linear | X | R I **X** | R I | 3.3 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | R_cover |
| `lit_csf21_vehicle_thermo` | Literature | 3/3 | 6/6 | linear | X | R I **X** | R I | 2.9 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | R_cover |
| `lit_csf25_salt_tank_hold` | Literature | 2/2 | 2/2 | linear | S D I | **S** **D** **I** | - | 0.2 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | HoldInc:DECLINED (drops a stated row), HoldDec:DECLINED (drops a stated row), conj:DECLINED | S_lam1 D_rows D_strict |
| `lit_drl_lane_control` | Literature | 3/3 | 6/6 | linear | X | R I **X** | R I | 4.2 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | R_cover |
| `lit_freedm_meter` | Literature | 2/2 | 12/12 | linear | X | R I **X** | R I | 2.3 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | R_cover |
| `lit_girard08_robot` | Literature | 6/2 | 6/6 | quadratic | X | R I **X** | R I | 56.1 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | R_cover |
| `lit_gpt10_boost_converter` | Literature | 2/2 | 48/2 | quadratic | X | I **X** | I | 46.6 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `lit_lz21_vehicle_position` | Literature | 2/2 | 3/3 | linear | X | R I **X** | R I | 0.5 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | R_cover |
| `lit_nahs25_engine_cooling` | Literature | 1/1 | 2/2 | linear | R | **R** | - | 0.1 | DECLINED | - | DECLINED | CERTIFIED | - | R_cover |
| `lit_nahs25_salt_tank` | Literature | 1/1 | 2/2 | linear | S | **S** I | I | 0.4 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | - | S_lam1 |
| `molding_pack_checkring` | Injection molding pack and hold | 3/3 | 2/2 | linear | D | **D** I | I | 0.4 | CERTIFIED | - | CERTIFIED | CERTIFIED | HOLD:DECLINED, COOL:DECLINED (drops a stated row) | D_rows D_strict |
| `platoon_linkloss` | Platoon follower (CACC: link loss, latency, profiles) | 2/2 | 2/1 | linear | -- | M I | M I | 0.1 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `platoon_profiles` | Platoon follower (CACC: link loss, latency, profiles) | 2/2 | 1/1 | linear | S | **S** M I | M I | 0.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `quad_light_lag` | Quadrotor climb, lighter airframe | 3/3 | 1/1 | linear | S | **S** M I | M I | 0.0 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `quad_light_profiles` | Quadrotor climb, lighter airframe | 2/2 | 3/3 | linear | S X | **S** M R B I **X** | M R B I | 10.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 R_cover |
| `rampmeter_poll_2to1` | Freeway ramp metering (polled detectors) | 3/3 | 6/6 | linear | -- | M B P I | M B P I | 11.9 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `reactor_feed_wireless` | Exothermic reactor feed interlock | 2/2 | 4/4 | linear | P | M B **P** I | M B I | 7.3 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `rover_terrain_2to4` | Terrain chain | 4/4 | 3/3 | linear | I | **I** | - | 0.7 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `rover_terrain_4to6` | Terrain chain | 6/6 | 3/3 | linear | I | **I** | - | 1.8 | CERTIFIED | - | CERTIFIED | CERTIFIED | - | - |
| `sat3w_detumble_phases` | Rigid-body detumbling (polynomial) | 6/6 | 2/3 | quadratic | I X | M P **I** **X** | M P | 20.1 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `sat_detumble_phases` | Rigid-body detumbling (polynomial) | 4/4 | 2/3 | quadratic | I X | M P **I** **X** | M P | 7.0 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `sat_detumble_weak` | Rigid-body detumbling (polynomial) | 4/4 | 1/4 | quadratic | S X | **S** M B P I **X** | M B P I | 3.9 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 |
| `stopline_drag` | Rover ladder | 4/4 | 3/3 | quadratic | D | **D** I | I | 1.1 | CERTIFIED | - | CERTIFIED | CERTIFIED | CRUISE:DECLINED (drops a stated row), BRAKE:DECLINED (drops a stated row), STOP:DECLINED (drops a stated row), conj:DECLINED | D_rows D_strict |
| `stopline_friction` | Rover ladder | 3/3 | 3/3 | quadratic | S D | **S** **D** I | I | 0.6 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | CRUISE:DECLINED (drops a stated row), BRAKE:DECLINED (drops a stated row), STOP:DECLINED (drops a stated row), conj:DECLINED | S_lam1 D_rows D_strict |
| `stopline_lag` | Rover ladder | 3/3 | 3/3 | quadratic | D | **D** I | I | 0.2 | CERTIFIED | - | CERTIFIED | CERTIFIED | CRUISE:DECLINED (drops a stated row), BRAKE/STOP:DECLINED (drops a stated row), conj:DECLINED | D_rows D_strict |
| `stopline_tyre` | Rover ladder | 4/4 | 3/3 | quadratic | D | **D** I | I | 0.5 | CERTIFIED | - | CERTIFIED | CERTIFIED | CRUISE:DECLINED (drops a stated row), BRAKE/STOP:DECLINED (drops a stated row), conj:DECLINED | D_rows D_strict |
| `syringe_relay_prearm` | Syringe-pump relay | 4/4 | 6/4 | linear | R D | **R** **D** I | I | 1.9 | DECLINED | - | DECLINED | CERTIFIED | RUN1/PREARM/READY/TAKEUP2:DECLINED, RUN2/END:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `tank_dos_3to1` | Tank under sampling DoS | 2/2 | 4/4 | linear | I | M **I** | M | 1.2 | CERTIFIED | - | CERTIFIED | DECLINED | - | - |
| `train_ato_odometry` | Train speed control (ATO) | 1/1 | 3/3 | linear | S | **S** M B I | M B I | 2.2 | DECLINED | DECLINED | CERTIFIED | CERTIFIED | - | S_lam1 |
| `turbine_startup_gearratio` | Wind turbine start-up | 3/3 | 5/5 | linear | R D I | **R** **D** **I** | - | 0.9 | DECLINED | - | DECLINED | CERTIFIED | SPINUP/RAMP/GEN:DECLINED (drops a stated row), REG/GUST:CERTIFIED (drops a stated row), conj:DECLINED | R_cover D_rows |
| `ventilator_vc_cuffleak` | Volume-controlled ventilation | 2/2 | 2/2 | linear | D I | **D** **I** | - | 0.2 | CERTIFIED | - | CERTIFIED | CERTIFIED | INSP:DECLINED (drops a stated row), EXP:DECLINED (drops a stated row), conj:DECLINED | D_rows D_strict |
| `watertank` | Watertank | 1/1 | 3/5 | linear | S | **S** M R B P I | M R B P I | 1.1 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 R_cover |
| `watertank_twospeed` | Watertank | 1/1 | 3/6 | linear | S | **S** M R B I | M R B I | 1.7 | DECLINED | DECLINED | CERTIFIED | DECLINED | - | S_lam1 R_cover |

Totals (needed, the `letters` field and `\numletter<L>`; none for M, B): S 18, R 8, P 2, D 16, I 15, X 12

Totals (used, `\numletter<L>used`): S 18, M 19, R 19, B 9, P 8, D 17, I 49, X 12

Used and needed (2026-10-30): see the docstring of scripts/suite_v2_letters.py. Needed = the ablation rule (with the mechanism switched off the tool declines; M and B have no switch-off and are never needed). Used = the mechanism appears in the certificate the tool produced (S a stretch other than 1, 0 included; M a multi-step cover; R a right-only node; B a joint step with >= 2 retained successors; P any pruned edge; D rows that differ per left mode; I a checked cut kept in the certificate; X a committed successor subset). No other screens (owner's decision 2026-10-30, replacing the batch-11 screens).

D rule (2026-10-27): the stated requirement differs per mode, so the claim needs mode-dependent rows: matrix M5 and every uniform row set from the file's own rows that keeps every stated requirement declines; a uniform row marked (drops a stated row) may certify without removing D. Under the earlier strict rule (every uniform row set declines, diagnostic D_strict) D = 12.
