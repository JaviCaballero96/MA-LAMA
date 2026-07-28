; 3 drones, 16 waypoints, 7 targets

(define (problem drone_problem3)

(:domain drone_domainB)

(:objects
    base1_ground base1_air base2_ground base2_air base3_ground base3_air vp1 vp2 vp3 vp4 vp5 vp6 vp7 wp1 wp2 wp3 - waypoint
    tgt1 tgt2 tgt3 tgt4 tgt5 tgt6 tgt7 - target
    drone1 drone2 drone3 - drone
)

; --- INIT ---
(:init
    ; CONFIGURACIÓN DE PARÁMETROS
    (= (photo_time) 5.00) ; segundos para tomar una fotografía
    (= (recharge_rate) 10.00) ; cantidad de carga por segundo

    ; parámetros de velocidad de despegue y aterrizaje
    (= (takeoff_speed) 1.00)
    (= (land_speed) 0.50)

    ; parámetros para no quedarnos sin batería
    (= (battery_safety_margin base1_ground) 1.00)
    (= (battery_safety_margin base1_air) 20.00)
    (= (battery_safety_margin base2_ground) 1.00)
    (= (battery_safety_margin base2_air) 20.00)
    (= (battery_safety_margin base3_ground) 1.00)
    (= (battery_safety_margin base3_air) 20.00)
    (= (battery_safety_margin vp1) 20.00)
    (= (battery_safety_margin vp2) 20.00)
    (= (battery_safety_margin vp3) 20.00)
    (= (battery_safety_margin vp4) 20.00)
    (= (battery_safety_margin vp5) 20.00)
    (= (battery_safety_margin vp6) 20.00)
    (= (battery_safety_margin vp7) 20.00)
    (= (battery_safety_margin wp1) 20.00)
    (= (battery_safety_margin wp2) 20.00)
    (= (battery_safety_margin wp3) 20.00)

    ; CONFIGURACIÓN DE DRONE1
    (drone_at drone1 base1_ground) (available drone1)
    (= (battery_level drone1) 100.00)
    (= (battery_capacity drone1) 100.00)
    (= (drone_speed drone1) 1.00) ; m/s

    ; CONFIGURACIÓN DE DRONE2
    (drone_at drone2 base2_ground) (available drone2)
    (= (battery_level drone2) 100.00)
    (= (battery_capacity drone2) 100.00)
    (= (drone_speed drone2) 2.00) ; m/s

    ; CONFIGURACIÓN DE DRONE3
    (drone_at drone3 base3_ground) (available drone3)
    (= (battery_level drone3) 100.00)
    (= (battery_capacity drone3) 100.00)
    (= (drone_speed drone3) 3.00) ; m/s

    ; TIPOS DE WAYPOINT
    (is_ground base1_ground)
    (is_ground base2_ground)
    (is_ground base3_ground)
    (is_air base1_air) (is_air base2_air) (is_air base3_air) (is_air vp1) (is_air vp2) (is_air vp3) (is_air vp4) (is_air vp5) (is_air vp6) (is_air vp7) (is_air wp1) (is_air wp2) (is_air wp3)

    ; CONFIGURACIÓN DE LAS BASES
    (is_recharge base1_ground)
    (is_recharge base2_ground)
    (is_recharge base3_ground)

    ; WAYPOINTS LIBRES (las bases de suelo NO estan libres: las ocupan los drones)
    (free base1_air) (free base2_air) (free base3_air)
    (free vp1) (free vp2) (free vp3) (free vp4) (free vp5) (free vp6) (free vp7)
    (free wp1) (free wp2) (free wp3)

    ; TARGETS PENDIENTES DE FOTOGRAFIAR
    (pending tgt1) (pending tgt2) (pending tgt3) (pending tgt4)
    (pending tgt5) (pending tgt6) (pending tgt7)

    ; RELACIÓN SUELO <-> AIRE (solo se transita con takeoff / land)
    ; base1_ground <-> base1_air  (3.00 m de altitud)
    (landing_pad base1_ground base1_air)
    (= (distance base1_ground base1_air) 3.00) (= (takeoff_cost base1_ground base1_air) 2.00)
    (= (distance base1_air base1_ground) 3.00) (= (land_cost base1_air base1_ground) 1.00)
    ; base2_ground <-> base2_air  (3.00 m de altitud)
    (landing_pad base2_ground base2_air)
    (= (distance base2_ground base2_air) 3.00) (= (takeoff_cost base2_ground base2_air) 2.00)
    (= (distance base2_air base2_ground) 3.00) (= (land_cost base2_air base2_ground) 1.00)
    ; base3_ground <-> base3_air  (3.00 m de altitud)
    (landing_pad base3_ground base3_air)
    (= (distance base3_ground base3_air) 3.00) (= (takeoff_cost base3_ground base3_air) 2.00)
    (= (distance base3_air base3_ground) 3.00) (= (land_cost base3_air base3_ground) 1.00)

    ; CONECTIVIDAD ENTRE PUNTOS (distancia y coste calculados por geometría)
    ; base1_air <-> vp1  (6.52 m)
    (valid_path base1_air vp1) (= (distance base1_air vp1) 6.52) (= (fly_cost base1_air vp1) 0.65)
    (valid_path vp1 base1_air) (= (distance vp1 base1_air) 6.52) (= (fly_cost vp1 base1_air) 0.65)

    ; vp1 <-> vp2  (5.66 m)
    (valid_path vp1 vp2) (= (distance vp1 vp2) 5.66) (= (fly_cost vp1 vp2) 0.57)
    (valid_path vp2 vp1) (= (distance vp2 vp1) 5.66) (= (fly_cost vp2 vp1) 0.57)

    ; base2_air <-> vp3  (12.42 m)
    (valid_path base2_air vp3) (= (distance base2_air vp3) 12.42) (= (fly_cost base2_air vp3) 1.24)
    (valid_path vp3 base2_air) (= (distance vp3 base2_air) 12.42) (= (fly_cost vp3 base2_air) 1.24)

    ; vp3 <-> vp4  (4.31 m)
    (valid_path vp3 vp4) (= (distance vp3 vp4) 4.31) (= (fly_cost vp3 vp4) 0.43)
    (valid_path vp4 vp3) (= (distance vp4 vp3) 4.31) (= (fly_cost vp4 vp3) 0.43)

    ; vp2 <-> vp4  (7.07 m)
    (valid_path vp2 vp4) (= (distance vp2 vp4) 7.07) (= (fly_cost vp2 vp4) 0.71)
    (valid_path vp4 vp2) (= (distance vp4 vp2) 7.07) (= (fly_cost vp4 vp2) 0.71)

    ; vp1 <-> wp1  (1.53 m)
    (valid_path vp1 wp1) (= (distance vp1 wp1) 1.53) (= (fly_cost vp1 wp1) 0.15)
    (valid_path wp1 vp1) (= (distance wp1 vp1) 1.53) (= (fly_cost wp1 vp1) 0.15)

    ; vp2 <-> wp1  (7.09 m)
    (valid_path vp2 wp1) (= (distance vp2 wp1) 7.09) (= (fly_cost vp2 wp1) 0.71)
    (valid_path wp1 vp2) (= (distance wp1 vp2) 7.09) (= (fly_cost wp1 vp2) 0.71)

    ; vp3 <-> wp1  (9.84 m)
    (valid_path vp3 wp1) (= (distance vp3 wp1) 9.84) (= (fly_cost vp3 wp1) 0.98)
    (valid_path wp1 vp3) (= (distance wp1 vp3) 9.84) (= (fly_cost wp1 vp3) 0.98)

    ; vp4 <-> wp1  (10.41 m)
    (valid_path vp4 wp1) (= (distance vp4 wp1) 10.41) (= (fly_cost vp4 wp1) 1.04)
    (valid_path wp1 vp4) (= (distance wp1 vp4) 10.41) (= (fly_cost wp1 vp4) 1.04)

    ; base3_air <-> vp2  (2.71 m)
    (valid_path base3_air vp2) (= (distance base3_air vp2) 2.71) (= (fly_cost base3_air vp2) 0.27)
    (valid_path vp2 base3_air) (= (distance vp2 base3_air) 2.71) (= (fly_cost vp2 base3_air) 0.27)

    ; vp5 <-> vp6  (3.96 m)
    (valid_path vp5 vp6) (= (distance vp5 vp6) 3.96) (= (fly_cost vp5 vp6) 0.40)
    (valid_path vp6 vp5) (= (distance vp6 vp5) 3.96) (= (fly_cost vp6 vp5) 0.40)

    ; vp1 <-> vp6  (5.61 m)
    (valid_path vp1 vp6) (= (distance vp1 vp6) 5.61) (= (fly_cost vp1 vp6) 0.56)
    (valid_path vp6 vp1) (= (distance vp6 vp1) 5.61) (= (fly_cost vp6 vp1) 0.56)

    ; vp1 <-> vp7  (4.89 m)
    (valid_path vp1 vp7) (= (distance vp1 vp7) 4.89) (= (fly_cost vp1 vp7) 0.49)
    (valid_path vp7 vp1) (= (distance vp7 vp1) 4.89) (= (fly_cost vp7 vp1) 0.49)

    ; vp4 <-> wp2  (2.44 m)
    (valid_path vp4 wp2) (= (distance vp4 wp2) 2.44) (= (fly_cost vp4 wp2) 0.24)
    (valid_path wp2 vp4) (= (distance wp2 vp4) 2.44) (= (fly_cost wp2 vp4) 0.24)

    ; vp3 <-> wp2  (4.47 m)
    (valid_path vp3 wp2) (= (distance vp3 wp2) 4.47) (= (fly_cost vp3 wp2) 0.45)
    (valid_path wp2 vp3) (= (distance wp2 vp3) 4.47) (= (fly_cost wp2 vp3) 0.45)

    ; vp2 <-> wp2  (5.28 m)
    (valid_path vp2 wp2) (= (distance vp2 wp2) 5.28) (= (fly_cost vp2 wp2) 0.53)
    (valid_path wp2 vp2) (= (distance wp2 vp2) 5.28) (= (fly_cost wp2 vp2) 0.53)

    ; vp6 <-> wp1  (4.82 m)
    (valid_path vp6 wp1) (= (distance vp6 wp1) 4.82) (= (fly_cost vp6 wp1) 0.48)
    (valid_path wp1 vp6) (= (distance wp1 vp6) 4.82) (= (fly_cost wp1 vp6) 0.48)

    ; vp7 <-> wp1  (5.02 m)
    (valid_path vp7 wp1) (= (distance vp7 wp1) 5.02) (= (fly_cost vp7 wp1) 0.50)
    (valid_path wp1 vp7) (= (distance wp1 vp7) 5.02) (= (fly_cost wp1 vp7) 0.50)

    ; CONFIGURACIÓN DE LOS PUNTOS DE FOTOGRAFÍA
    (can_photograph vp1 tgt1)
    (can_photograph vp2 tgt2)
    (can_photograph vp3 tgt3)
    (can_photograph vp4 tgt4)
    (can_photograph vp5 tgt5)
    (can_photograph vp6 tgt6)
    (can_photograph vp7 tgt7)

)

; --- GOAL ---
(:goal
    (and
        (photographed tgt1)
        (photographed tgt2)
        (photographed tgt3)
        (photographed tgt4)
        (photographed tgt5)
        (photographed tgt6)
        (photographed tgt7)

        (drone_at drone1 base1_ground)
        (drone_at drone2 base2_ground)
        (drone_at drone3 base3_ground)
    )
)

; --- METRIC ---
(:metric minimize (total-time))

)

