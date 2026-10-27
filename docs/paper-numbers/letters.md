| benchmark | family | dim L/R | modes L/R | inv | letters | time (s) | SYNC | lambda=1 file | NO_REPO | uniform rows | diagnostics |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `acc_spoof_lag` | ACC under sensor spoofing / retune | 2/2 | 1/1 | linear | I | 0.1 | CERTIFIED | - | CERTIFIED | - | - |
| `acc_spoof_limp` | ACC under sensor spoofing / retune | 1/1 | 2/4 | linear | M B I | 0.2 | CERTIFIED | - | CERTIFIED | - | - |
| `acc_tune_lag` | ACC under sensor spoofing / retune | 2/2 | 1/1 | linear | S M | 0.1 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `acc_tune_limp` | ACC under sensor spoofing / retune | 1/1 | 2/4 | linear | S M B I X | 1.0 | DECLINED | DECLINED | CERTIFIED | CRUISE:DECLINED, LIMP:CERTIFIED | S_lam1 D_rows |
| `antenna_track_kvretune` | Ground-station antenna (servo retune) | 3/3 | 3/3 | linear | -- | 0.9 | CERTIFIED | - | CERTIFIED | TRACK:DECLINED, STOW/STOWED:CERTIFIED | D_rows |
| `bms_chiller_undercharge` | Battery pack thermal management (chiller) | 1/1 | 2/3 | linear | X | 0.1 | CERTIFIED | - | CERTIFIED | - | - |
| `bottling_fill_strainer` | Bottle filler (clogged product strainer) | 2/2 | 2/2 | linear | S I | 0.6 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `charger_fast_tapers` | DC fast charger (raised current limit) | 1/1 | 5/6 | linear | R P D I | 0.5 | DECLINED | - | DECLINED | PRECHARGE:DECLINED, BULK/ABSORB/FULL/FAULT:DECLINED | R_cover D_rows |
| `compressor_station_recycle` | Gas compressor station | 2/2 | 3/3 | linear | X | 0.4 | CERTIFIED | - | CERTIFIED | - | - |
| `csf21_vehicle_bus` | Literature | 3/3 | 6/12 | linear | X | 3.4 | CERTIFIED | - | CERTIFIED | - | - |
| `csf21_vehicle_thermo` | Literature | 3/3 | 6/6 | linear | X | 1.7 | CERTIFIED | - | CERTIFIED | - | - |
| `drl_car_stop` | Literature | 2/2 | 3/3 | linear | X | 0.4 | CERTIFIED | - | CERTIFIED | - | - |
| `drl_lane_control` | Literature | 3/3 | 6/6 | linear | X | 2.7 | CERTIFIED | - | CERTIFIED | - | - |
| `elevator_start_discbrake` | Elevator trip | 3/3 | 4/4 | linear | R D | 1.0 | DECLINED | - | DECLINED | LIFT:DECLINED, UP/APP/STOP:DECLINED | R_cover D_rows |
| `engine_start_highidle` | Turbofan ground start | 1/1 | 5/5 | linear | R D I | 0.4 | DECLINED | - | DECLINED | STARTER/LIGHTOFF:DECLINED, SELF/IDLE/ABORT:DECLINED | R_cover D_rows |
| `freedm_meter` | Literature | 2/2 | 12/12 | linear | X | 2.3 | CERTIFIED | - | CERTIFIED | - | - |
| `fuelcell_chp_dos` | Fuel-cell CHP current levels | 2/2 | 3/3 | linear | M B P X | 0.4 | CERTIFIED | - | CERTIFIED | - | - |
| `furnace_program_timebase` | Heat-treatment furnace program | 2/2 | 3/3 | linear | S I | 1.1 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `gantry_speed_zones` | Gantry speed zones (multi-cycle matching) | 2/2 | 3/1 | linear | S M | 1.2 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `girard_robot` | Literature | 6/2 | 6/6 | quadratic | X | 3.6 | CERTIFIED | - | CERTIFIED | - | - |
| `grid_ffr_dos` | Island grid fast frequency response (DoS on the FFR link) | 3/3 | 2/3 | linear | M P | 0.4 | CERTIFIED | - | CERTIFIED | - | - |
| `hydro_rejection_gatecal` | Hydro unit load rejection | 3/3 | 2/2 | linear | D | 0.3 | CERTIFIED | - | CERTIFIED | ONGRID:DECLINED, REJECT:DECLINED | D_rows |
| `insulin_basal_cgmloss` | Insulin basal control | 3/3 | 9/9 | linear | M B | 6.7 | CERTIFIED | - | CERTIFIED | - | - |
| `lz_vehicle_position` | Literature | 2/2 | 3/3 | linear | X | 0.3 | CERTIFIED | - | CERTIFIED | - | - |
| `molding_pack_checkring` | Injection molding pack and hold | 3/3 | 2/2 | linear | D | 0.3 | CERTIFIED | - | CERTIFIED | HOLD:DECLINED, COOL:DECLINED | D_rows |
| `platoon_latency` | Platoon follower (CACC, link loss / latency) | 3/2 | 3/2 | linear | D | 0.6 | CERTIFIED | - | CERTIFIED | CACC_UP/CACC_DN:DECLINED, AEB:DECLINED | D_rows |
| `platoon_linkloss` | Platoon follower (CACC, link loss / latency) | 2/2 | 3/2 | linear | D | 0.6 | CERTIFIED | - | CERTIFIED | CACC/ACC:DECLINED, AEB:DECLINED | D_rows |
| `quad_light_lag` | Quadrotor climb, lighter airframe | 3/3 | 1/1 | linear | S M | 0.1 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `quad_light_profiles` | Quadrotor climb, lighter airframe | 2/2 | 1/3 | linear | X | 0.2 | CERTIFIED | - | CERTIFIED | - | - |
| `rover_ladder_2to3` | Rover ladder | 3/3 | 3/3 | linear | -- | 0.3 | CERTIFIED | - | CERTIFIED | - | - |
| `rover_ladder_3to6` | Rover ladder | 6/6 | 3/3 | linear | -- | 0.7 | CERTIFIED | - | CERTIFIED | - | - |
| `rover_ladder_6to8` | Rover ladder | 8/8 | 3/3 | quadratic | S M I | 18.6 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `rover_ladder_8to12` | Rover ladder | 12/12 | 3/3 | quadratic | S M I | 34.8 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `rover_patrol_lag` | Rover patrol (zones) | 3/2 | 4/4 | linear | S M R B | 1.3 | DECLINED | DECLINED | DECLINED | - | S_lam1 R_cover |
| `rover_terrain_2to4` | Terrain chain | 4/4 | 3/3 | linear | I | 0.4 | CERTIFIED | - | CERTIFIED | - | - |
| `rover_terrain_4to6` | Terrain chain | 6/6 | 3/3 | linear | I | 1.2 | CERTIFIED | - | CERTIFIED | - | - |
| `rover_terrain_6to12` | Terrain chain | 12/12 | 3/3 | linear | I | 2.3 | CERTIFIED | - | CERTIFIED | - | - |
| `salt_tank_sensor` | Literature | 1/1 | 2/2 | linear | I | 0.1 | CERTIFIED | - | CERTIFIED | - | - |
| `sat3w_detumble_phases` | Rigid-body detumbling (polynomial) | 6/6 | 2/3 | quadratic | X | 2.4 | CERTIFIED | - | CERTIFIED | - | - |
| `sat_detumble_phases` | Rigid-body detumbling (polynomial) | 4/4 | 2/3 | quadratic | X | 4.5 | CERTIFIED | - | CERTIFIED | - | - |
| `sat_detumble_weak` | Rigid-body detumbling (polynomial) | 4/4 | 1/4 | quadratic | I X | 8.1 | CERTIFIED | - | CERTIFIED | - | - |
| `syringe_relay_prearm` | Syringe-pump relay | 4/4 | 6/4 | linear | R D | 1.3 | DECLINED | - | DECLINED | RUN1/PREARM/READY/TAKEUP2:DECLINED, RUN2/END:DECLINED | R_cover D_rows |
| `tank_dos_3to1` | Tank under sampling DoS | 2/2 | 4/4 | linear | M I | 1.0 | CERTIFIED | - | CERTIFIED | - | - |
| `train_ato_odometry` | Train speed control (ATO) | 1/1 | 3/3 | linear | S M B | 2.5 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `tunnel_jetfan_pairout` | Road-tunnel ventilation through a fire alarm | 3/3 | 2/2 | linear | I | 0.2 | CERTIFIED | - | CERTIFIED | NORMAL:DECLINED, FIRE:CERTIFIED | D_rows |
| `turbine_startup_gearratio` | Wind turbine start-up | 1/1 | 4/4 | linear | R P I | 0.3 | DECLINED | - | DECLINED | - | R_cover |
| `vehicle_hypercert` | Literature | 2/2 | 5/5 | linear | X | 1.0 | CERTIFIED | - | CERTIFIED | - | - |
| `ventilator_vc_cuffleak` | Volume-controlled ventilation | 2/2 | 2/2 | linear | D | 0.2 | CERTIFIED | - | CERTIFIED | INSP:DECLINED, EXP:DECLINED | D_rows |
| `watertank` | Watertank | 1/1 | 3/5 | linear | S M B | 0.7 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |
| `watertank_twospeed` | Watertank | 1/1 | 3/6 | linear | S M B P | 2.0 | DECLINED | DECLINED | CERTIFIED | - | S_lam1 |

Totals: S 12, M 15, R 6, B 8, P 5, D 9, I 17, X 16
