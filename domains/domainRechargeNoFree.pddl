(define (domain MoBAr-Rover)
   (:requirements :strips :typing :fluents :durative-actions :adl :preferences :constraints)
   (:types
     Loc Agent NavMode ICam - Object
   )
   (:predicates
		 (modeTransition ?n1 - NavMode ?n2 - NavMode)
	   (Navigation_Mode ?a - Agent ?n - NavMode)
		 (Communication_transmittedP ?p - Loc)
		 (RobotBase_NotOnDock ?a - Agent)
		 (RobotBase_OnDock ?a - Agent)
		 (RobotBase_At ?a - Agent ?p - Loc)
		 (Cameras_Picture ?a - Agent ?p - Loc)
		 (traversable ?p1 - Loc ?p2 - Loc)
		 (inside ?i - ICam ?a - Agent)
		 (visited ?p - Loc)
		 (dockPos ?p - Loc)
   )

	 (:functions
		 (batperdis ?a - Agent ?n - NavMode)
     (distance_to_move ?p1 ?p2 - Loc)
		 (speed ?a - Agent ?n - NavMode)
		 (metricPercentage ?a - Agent)
		 (battery_avail ?a - Agent)
		 (battery ?a - Agent)
		 (posRisk ?p - Loc)
		 (dist ?a - Agent)
		 (risk ?a - Agent)
		 (energyTransPhoto)
		 (timeChangeMode)
		 (timeTransPhoto)
		 (time_recharge)
		 (photoEnergy)
		 (max_battery)
		 (timePhoto)
		 (timeDock)
		 (total_dist)
   )

   (:durative-action RobotBase_GoingTo
     :parameters (?a - Agent ?n - NavMode ?p1 - Loc ?p - Loc)
     :duration (= ?duration (/ (distance_to_move ?p1 ?p)(speed ?a ?n)))
     :condition (and
				(over all (Navigation_Mode ?a ?n))
				(over all (traversable ?p1 ?p))
				(at start (RobotBase_NotOnDock ?a))
      	(at start (RobotBase_At ?a ?p1))
      )
     :effect (and
				(at start (not (RobotBase_At ?a ?p1)))
				(at end (visited ?p))
        (at end (RobotBase_At ?a ?p))
				(at end (increase (risk ?a) (posRisk ?p)))
				(at end (increase (dist ?a) (distance_to_move ?p1 ?p)))
        (at end (increase (total_dist) (distance_to_move ?p1 ?p)))
				(at end (increase (battery ?a) (* (distance_to_move ?p1 ?p) (batperdis ?a ?n))))
				(at end (decrease (battery_avail ?a) (* (distance_to_move ?p1 ?p) (batperdis ?a ?n))))
     )
   )

	 (:durative-action Navigation_ChangeMode
		 :parameters (?a - Agent ?n1 - NavMode ?n2 - NavMode)
		 :duration (= ?duration (timeChangeMode))
		 :condition (and
			 (at start (Navigation_Mode ?a ?n1))
			 (at start (RobotBase_OnDock ?a))
			 (over all (modeTransition ?n1 ?n2))
			 )
		 :effect (and
			 (at start (not (Navigation_Mode ?a ?n1)))
			 (at end (Navigation_Mode ?a ?n2))
			 )
		)

		(:durative-action Cameras_TakingPicture
			:parameters (?a - Agent ?p - Loc ?i - ICam)
			:duration (= ?duration (timePhoto) )
			:condition (and
								 (over all (RobotBase_At ?a ?p))
								 (over all (inside ?i ?a))
								 )
			:effect (and
								 (at end (Cameras_Picture ?a ?p))
								 (at end (increase (battery ?a) (photoEnergy)))
						     )
		)

		(:durative-action Communication_TransmittingPicture
			:parameters (?a - Agent ?p - Loc)
			:duration (= ?duration (timeTransPhoto))
			:condition (and
								 (over all (Cameras_Picture ?a ?p))
								 )
			:effect (and
								 (at end (Communication_transmittedP ?p))
								 (at end (increase (battery ?a) (energyTransPhoto)))
							)
	 )

		(:durative-action RobotBase_Docking
      :parameters (?a - Agent ?p - Loc)
      :duration (= ?duration (timeDock))
      :condition (and
				         (at start (dockPos ?p))
                 (at start (RobotBase_At ?a ?p))
                 (at start (RobotBase_NotOnDock ?a))
                 )
      :effect (and
								 (at start (not (RobotBase_NotOnDock ?a)))
                 (at end (RobotBase_OnDock ?a))
                 )
    )

		(:durative-action RobotBase_Undocking
			:parameters (?a - Agent ?p - Loc)
			:duration (= ?duration (timeDock))
			:condition (and
								 (at start (dockPos ?p))
								 (at start (RobotBase_At ?a ?p))
								 (at start (RobotBase_OnDock ?a))
								 )
			:effect (and
								 (at start (not (RobotBase_OnDock ?a)))
								 (at end (RobotBase_NotOnDock ?a))
								 )
		)

		(:durative-action RobotBase_Recharge
			:parameters (?a - Agent ?p - Loc)
			:duration (= ?duration (time_recharge))
			:condition (and
								 (at start (dockPos ?p))
								 (at start (RobotBase_At ?a ?p))
								 (at start (RobotBase_OnDock ?a))
								 )
			:effect (and
								 (at end (assign (battery_avail ?a) (max_battery)))
								 )
		)
)
