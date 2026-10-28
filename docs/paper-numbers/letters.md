| benchmark | family | dim L/R | modes L/R | inv | letters | time (s) | SYNC | lambda=1 file | NO_REPO | uniform rows | diagnostics |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | ACC under sensor spoofing / retune | 2/2 | 1/1 | linear | S M | 0.2 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `acc_spoof_limp` | ACC under sensor spoofing / retune | 1/1 | 2/4 | linear | M B I | 0.2 | CERTIFIED | - | CERTIFIED | - | - |
| `acc_tune_lag` | ACC under sensor spoofing / retune | 2/2 | 1/1 | linear | S M | 0.1 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `acc_tune_limp` | ACC under sensor spoofing / retune | 1/1 | 2/4 | linear | S M B D I X | 1.0 | DECLINED | DECLINED | CERTIFIED | CRUISE:DECLINED, LIMP:CERTIFIED (drops a stated row) | S_lam1 D_rows |
| `bottling_fill_strainer` | Bottle filler (clogged product strainer) | 2/2 | 2/2 | linear | S I | 0.6 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `charger_fast_tapers` | DC fast charger (raised current limit) | 1/1 | 5/6 | linear | M R B P D I | 0.5 | DECLINED | - | DECLINED | PRECHARGE:DECLINED, BULK/ABSORB/FULL/FAULT:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `elevator_start_discbrake` | Elevator trip | 3/3 | 4/4 | linear | R D | 1.0 | DECLINED | - | DECLINED | LIFT:DECLINED, UP/APP/STOP:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `engine_start_highidle` | Turbofan ground start | 1/1 | 5/5 | linear | R D I | 0.4 | DECLINED | - | DECLINED | STARTER/LIGHTOFF:DECLINED, SELF/IDLE/ABORT:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `flaps_slow_approach` | Airliner flap extension (one hydraulic system lost) | 2/2 | 2/2 | linear | S | 0.2 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `fuelcell_chp_dos` | Fuel-cell CHP current levels | 2/2 | 3/3 | linear | M B P X | 0.4 | CERTIFIED | - | CERTIFIED | - | - |
| `furnace_program_timebase` | Heat-treatment furnace program | 2/2 | 3/3 | linear | S I | 1.1 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `gantry_speed_zones` | Gantry speed zones (multi-cycle matching) | 2/2 | 3/1 | linear | S M | 1.2 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `grid_ffr_dos` | Island grid fast frequency response (DoS on the FFR link) | 3/3 | 2/3 | linear | M P | 0.4 | CERTIFIED | - | CERTIFIED | - | - |
| `h2_refuel_ambientbias` | Hydrogen refuelling (sensor bias) | 1/1 | 6/6 | linear | R D I | 0.7 | DECLINED | - | DECLINED | STAGE1/STAGE2/STAGE3:DECLINED, TOPOFF/COMPLETE/ABORT:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `hydro_rejection_gatecal` | Hydro unit load rejection | 3/3 | 2/2 | linear | D | 0.3 | CERTIFIED | - | CERTIFIED | ONGRID:DECLINED, REJECT:DECLINED (drops a stated row) | D_rows D_strict |
| `lit_csf21_vehicle_bus` | Literature | 3/3 | 6/12 | linear | X | 3.5 | CERTIFIED | - | CERTIFIED | - | - |
| `lit_csf21_vehicle_thermo` | Literature | 3/3 | 6/6 | linear | X | 1.8 | CERTIFIED | - | CERTIFIED | - | - |
| `lit_drl_car_stop` | Literature | 2/2 | 3/3 | linear | X | 0.4 | CERTIFIED | - | CERTIFIED | - | - |
| `lit_drl_lane_control` | Literature | 3/3 | 6/6 | linear | X | 2.8 | CERTIFIED | - | CERTIFIED | - | - |
| `lit_freedm_meter` | Literature | 2/2 | 12/12 | linear | X | 2.4 | CERTIFIED | - | CERTIFIED | - | - |
| `lit_girard08_robot` | Literature | 6/2 | 6/6 | quadratic | X | 3.7 | CERTIFIED | - | CERTIFIED | - | - |
| `lit_hypercert_vehicle` | Literature | 2/2 | 5/5 | linear | X | 1.0 | CERTIFIED | - | CERTIFIED | - | - |
| `lit_lz21_vehicle_position` | Literature | 2/2 | 3/3 | linear | X | 0.3 | CERTIFIED | - | CERTIFIED | - | - |
| `lit_nahs25_salt_tank` | Literature | 1/1 | 2/2 | linear | I | 0.1 | CERTIFIED | - | CERTIFIED | - | - |
| `platoon_latency` | Platoon follower (CACC: link loss, latency, profiles) | 3/2 | 3/2 | linear | D | 0.6 | CERTIFIED | - | CERTIFIED | CACC_UP/CACC_DN:DECLINED (drops a stated row), AEB:DECLINED (drops a stated row), conj:DECLINED | D_rows D_strict |
| `platoon_linkloss` | Platoon follower (CACC: link loss, latency, profiles) | 2/2 | 3/2 | linear | M D | 0.6 | CERTIFIED | - | CERTIFIED | CACC/ACC:DECLINED (drops a stated row), AEB:DECLINED (drops a stated row), conj:DECLINED | D_rows D_strict |
| `platoon_profiles` | Platoon follower (CACC: link loss, latency, profiles) | 2/2 | 2/2 | linear | S M D | 2.3 | DECLINED | DECLINED | CERTIFIED | SPORT:DECLINED (drops a stated row), AEB:DECLINED (drops a stated row), conj:DECLINED | S_lam1 D_rows D_strict |
| `quad_light_lag` | Quadrotor climb, lighter airframe | 3/3 | 1/1 | linear | S M | 0.1 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `quad_light_profiles` | Quadrotor climb, lighter airframe | 2/2 | 1/3 | linear | S M B X | 0.2 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `reactor_feed_wireless` | Exothermic reactor feed interlock | 2/2 | 4/4 | linear | M B P | 0.7 | CERTIFIED | - | CERTIFIED | - | - |
| `rover_ladder_2to3` | Rover ladder | 3/3 | 3/3 | linear | -- | 0.3 | CERTIFIED | - | CERTIFIED | - | - |
| `rover_ladder_3to6` | Rover ladder | 6/6 | 3/3 | linear | -- | 0.7 | CERTIFIED | - | CERTIFIED | - | - |
| `rover_ladder_6to8` | Rover ladder | 8/8 | 3/3 | quadratic | S M I | 18.2 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `rover_ladder_8to12` | Rover ladder | 12/12 | 3/3 | quadratic | S M I | 32.9 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `rover_patrol_lag` | Rover patrol (zones) | 3/2 | 4/4 | linear | S M R B | 1.3 | DECLINED | DECLINED | DECLINED | - | S_lam1 R_cover |
| `rover_terrain_2to4` | Terrain chain | 4/4 | 3/3 | linear | S M I | 2.3 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `rover_terrain_4to6` | Terrain chain | 6/6 | 3/3 | linear | I | 1.1 | CERTIFIED | - | CERTIFIED | - | - |
| `rover_terrain_6to12` | Terrain chain | 12/12 | 3/3 | linear | I | 2.2 | CERTIFIED | - | CERTIFIED | - | - |
| `sat3w_detumble_phases` | Rigid-body detumbling (polynomial) | 6/6 | 2/3 | quadratic | M I X | 2.8 | CERTIFIED | - | CERTIFIED | - | - |
| `sat_detumble_phases` | Rigid-body detumbling (polynomial) | 4/4 | 2/3 | quadratic | M I X | 4.6 | CERTIFIED | - | CERTIFIED | - | - |
| `sat_detumble_weak` | Rigid-body detumbling (polynomial) | 4/4 | 1/4 | quadratic | S M B X | 2.0 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `syringe_relay_prearm` | Syringe-pump relay | 4/4 | 6/4 | linear | R D | 1.2 | DECLINED | - | DECLINED | RUN1/PREARM/READY/TAKEUP2:DECLINED, RUN2/END:DECLINED (drops a stated row) | R_cover D_rows D_strict |
| `tank_dos_3to1` | Tank under sampling DoS | 2/2 | 4/4 | linear | M I | 0.9 | CERTIFIED | - | CERTIFIED | - | - |
| `train_ato_odometry` | Train speed control (ATO) | 1/1 | 3/3 | linear | S M B | 2.3 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `tunnel_jetfan_pairout` | Road-tunnel ventilation through a fire alarm | 3/3 | 2/2 | linear | D I | 0.2 | CERTIFIED | - | CERTIFIED | NORMAL:DECLINED, FIRE:CERTIFIED (drops a stated row) | D_rows |
| `turbine_startup_gearratio` | Wind turbine start-up | 1/1 | 4/4 | linear | R P I | 0.3 | DECLINED | - | DECLINED | - | R_cover |
| `ventilator_vc_cuffleak` | Volume-controlled ventilation | 2/2 | 2/2 | linear | D | 0.2 | CERTIFIED | - | CERTIFIED | INSP:DECLINED (drops a stated row), EXP:DECLINED (drops a stated row), conj:DECLINED | D_rows D_strict |
| `watertank` | Watertank | 1/1 | 3/5 | linear | S M B | 0.6 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `watertank_twospeed` | Watertank | 1/1 | 3/6 | linear | S M B P | 1.9 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `zone_lightmass_schedule` | Building zone heating (lightweight construction) | 1/1 | 2/3 | linear | S M B X | 0.1 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |

Totals: S 19, M 25, R 7, B 12, P 6, D 12, I 18, X 15

D rule (2026-10-27): the stated requirement differs per mode, so the claim needs mode-dependent rows: matrix M5 and every uniform row set from the file's own rows that keeps every stated requirement declines; a uniform row marked (drops a stated row) may certify without removing D. Under the earlier strict rule (every uniform row set declines, diagnostic D_strict) D = 10.
