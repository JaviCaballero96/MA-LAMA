(define (domain drone_domainB)

(:requirements :typing :durative-actions :fluents)

(:types
    drone waypoint target - object
)

(:predicates
    (drone_at ?drone - drone ?wp - waypoint)
    (valid_path ?from - waypoint ?to - waypoint)
    (free ?wp - waypoint)                          ; sustituye a (not (ocupied ?wp))
    (is_ground ?wp - waypoint)
    (is_air ?wp - waypoint)
    (landing_pad ?ground - waypoint ?air - waypoint)
    (can_photograph ?wp - waypoint ?tgt - target)
    (photographed ?tgt - target)
    (pending ?tgt - target)                        ; sustituye a (not (photographed ?tgt))
    (available ?drone - drone)
    (is_recharge ?wp - waypoint)
    (visited_waypoint ?drone - drone ?wp - waypoint)
)

(:functions
    (battery_level ?drone - drone)
    (battery_capacity ?drone - drone)
    (battery_safety_margin ?wp - waypoint)
    (fly_cost ?from - waypoint ?to - waypoint)
    (takeoff_cost ?from - waypoint ?to - waypoint)
    (land_cost ?from - waypoint ?to - waypoint)
    (distance ?from - waypoint ?to - waypoint)
    (drone_speed ?drone - drone)
    (takeoff_speed)
    (land_speed)
    (photo_time)
    (recharge_rate)
)

; =====================================================================
;  FLY, desplazamiento entre waypoints aereos
; =====================================================================
(:durative-action fly
    :parameters (?from ?to - waypoint ?drone - drone)
    :duration (= ?duration (/ (distance ?from ?to) (drone_speed ?drone)))
    :condition (and
        (at start (drone_at ?drone ?from))
        (at start (available ?drone))
        (at start (valid_path ?from ?to))
        (at start (is_air ?from))
        (at start (is_air ?to))
        (at start (>= (battery_level ?drone) (battery_safety_margin ?to)))
        (at start (free ?to))
    )
    :effect (and
        (at start (not (drone_at ?drone ?from)))
        (at end (drone_at ?drone ?to))
        (at start (not (available ?drone)))
        (at end (available ?drone))
        (at end (decrease (battery_level ?drone) (fly_cost ?from ?to)))
        (at start (not (free ?to)))   ; reserva el destino al iniciar
        (at end (free ?from))         ; libera el origen al llegar
        (at end (visited_waypoint ?drone ?to))
    )
)

; =====================================================================
;  TAKEOFF, despegar de base_ground a base_air
; =====================================================================
(:durative-action takeoff
    :parameters (?ground ?air - waypoint ?drone - drone)
    :duration (= ?duration (/ (distance ?ground ?air) (takeoff_speed)))
    :condition (and
        (at start (drone_at ?drone ?ground))
        (at start (available ?drone))
        (at start (landing_pad ?ground ?air))
        (at start (is_ground ?ground))
        (at start (is_air ?air))
        (at start (>= (battery_level ?drone) (battery_safety_margin ?air)))
        (at start (free ?air))
    )
    :effect (and
        (at start (not (drone_at ?drone ?ground)))
        (at end (drone_at ?drone ?air))
        (at start (not (available ?drone)))
        (at end (available ?drone))
        (at end (decrease (battery_level ?drone) (takeoff_cost ?ground ?air)))
        (at start (not (free ?air)))    ; reserva el punto aereo al iniciar
        (at end (free ?ground))         ; libera el suelo al llegar
        (at end (visited_waypoint ?drone ?air))
    )
)

; =====================================================================
;  LAND, aterrizar de base_air a base_ground
; =====================================================================
(:durative-action land
    :parameters (?air ?ground - waypoint ?drone - drone)
    :duration (= ?duration (/ (distance ?air ?ground) (land_speed)))
    :condition (and
        (at start (drone_at ?drone ?air))
        (at start (available ?drone))
        (at start (landing_pad ?ground ?air))
        (at start (is_air ?air))
        (at start (is_ground ?ground))
        (at start (>= (battery_level ?drone) (battery_safety_margin ?ground)))
        (at start (free ?ground))
    )
    :effect (and
        (at start (not (drone_at ?drone ?air)))
        (at end (drone_at ?drone ?ground))
        (at start (not (available ?drone)))
        (at end (available ?drone))
        (at end (decrease (battery_level ?drone) (land_cost ?air ?ground)))
        (at start (not (free ?ground)))  ; reserva el suelo al iniciar
        (at end (free ?air))             ; libera el punto aereo al llegar
        (at end (visited_waypoint ?drone ?ground))
    )
)

; =====================================================================
;  TAKE_PHOTO, fotografiar un target desde un viewpoint valido
; =====================================================================
(:durative-action take_photo
    :parameters (?wp - waypoint ?drone - drone ?tgt - target)
    :duration (= ?duration (photo_time))
    :condition (and
        (at start (drone_at ?drone ?wp))
        (over all (drone_at ?drone ?wp))
        (at start (available ?drone))
        (at start (can_photograph ?wp ?tgt))
        (at start (pending ?tgt))
    )
    :effect (and
        (at start (not (available ?drone)))
        (at end (available ?drone))
        (at start (not (pending ?tgt)))
        (at end (photographed ?tgt))
        (at end (visited_waypoint ?drone ?wp))
    )
)

; =====================================================================
;  RECHARGE, recargar bateria hasta la capacidad maxima
; =====================================================================
(:durative-action recharge
    :parameters (?wp - waypoint ?drone - drone)
    :duration (= ?duration
                  (/ (- (battery_capacity ?drone) (battery_level ?drone))
                     (recharge_rate)))
    :condition (and
        (at start (drone_at ?drone ?wp))
        (over all (drone_at ?drone ?wp))
        (at start (available ?drone))
        (at start (is_recharge ?wp))
        (at start (< (battery_level ?drone) (battery_capacity ?drone)))
    )
    :effect (and
        (at start (not (available ?drone)))
        (at end (available ?drone))
        (at end (assign (battery_level ?drone) (battery_capacity ?drone)))
    )
)

)
