; Robots_carry_more_than_one_box/Without_addbox_action PDDL domain
(define (domain miptool_plus_domain)


(:requirements :typing :durative-actions :numeric-fluents :action-costs :timed-initial-literals)
(:types
	stringd float int robot box_stringd placeid_stringd - object
)

(:constants

	stringd_lab_pol stringd_lab_inter - placeid_stringd
)

(:predicates

    (robot_at ?robotid - robot ?place - placeid_stringd)
    (available ?robotid - robot)
    (collected ?boxid - box_stringd)

    (robot_has ?robotid - robot ?boxid - box_stringd)

    (on_time ?boxid - box_stringd)
    (box_at ?boxid - box_stringd ?place - placeid_stringd)
    (visited_place ?robotid - robot ?place - placeid_stringd)
    (associated_lab ?boxid - box_stringd ?labid - placeid_stringd)

    (valid_path ?from ?to - placeid_stringd)
    (is_lab ?labid - placeid_stringd)
)

(:functions

	(capacity_left ?robotid - robot)
	(weight ?boxid - box_stringd)

	(distance ?from ?to - placeid_stringd)
	(robot_speed ?robotid - robot)

	(manip_objects_time)
	(operation_time ?robotid - robot)


)

;;actions

(:durative-action go_to
	:parameters (?from ?to - placeid_stringd ?robot - robot)
	:duration (= ?duration (/ (distance ?from ?to) (robot_speed ?robot)))
	:condition (and

     (at start (robot_at ?robot ?from))
		 ;(at start (not (robot_at ?robot ?to)))

		 (at start (available ?robot))

		 (at start (valid_path ?from ?to))

		 ;(at start (not (visited_place ?robot ?to)))


	)
	:effect (and

		(at start (not (robot_at ?robot ?from)))
		(at end (robot_at ?robot ?to))

		(at start (not (available ?robot )))
		(at end (available ?robot ))

		(at start (assign (operation_time ?robot) (manip_objects_time)))
		(at start (visited_place ?robot ?to))


	)
)

(:durative-action load
 	:parameters (?at - placeid_stringd ?robotid - robot ?boxid - box_stringd)
 	:duration (= ?duration (operation_time ?robotid))
 	:condition (and

    (at start (robot_at ?robotid ?at))

 		(at start (box_at ?boxid ?at))

 		;(at start (not (is_lab ?at)))

 		;(at start (not (robot_has ?robotid ?boxid)))

 		(at start (available ?robotid ))

 		(at start (>= (capacity_left ?robotid ) (weight ?boxid)))

 	)
 	:effect (and

 		(at start (not (box_at ?boxid ?at)))

 		(at end (robot_has ?robotid ?boxid))

 		(at start (not (available ?robotid )))
 		(at end (available ?robotid ))

 		(at end (decrease (capacity_left ?robotid ) (weight ?boxid) ))

 		;(forall (?place - placeid_stringd) (at start (not (visited_place ?robotid ?place))))

 		(at end (visited_place ?robotid ?at))

		;(at end (assign (operation_time ?robotid) 0.01)) ; If there are multiple load operations in the same placeid_stringd, from the second one the loading time is negligible.


 	)
 )




(:durative-action unload_lab
	:parameters (?labid - placeid_stringd ?robotid - robot ?boxid - box_stringd)
	:duration (= ?duration (operation_time ?robotid))
	:condition (and

    (at start (robot_at ?robotid ?labid))

		(at start (robot_has ?robotid ?boxid))

		(at start (available ?robotid ))

		(over all (on_time ?boxid))

		;(at start (not (collected ?boxid )))

		(at start (associated_lab ?boxid ?labid))

		(at start (is_lab ?labid))


	)
	:effect (and

		(at start (not (robot_has ?robotid ?boxid)))

		(at start (not (available ?robotid )))
		(at end (available ?robotid ))

		(at end (increase (capacity_left ?robotid ) (weight ?boxid) ))

		(at end (collected ?boxid))
		;(at end (assign (operation_time ?robotid) 0.01))  ; If there are multiple unload operations in the same placeid_stringd, from the second one the unloading time is negligible.

		;(forall (?place - placeid_stringd) (at start (not (visited_place ?robotid ?place))))

		(at end (visited_place ?robotid ?labid))

	)
)


)
