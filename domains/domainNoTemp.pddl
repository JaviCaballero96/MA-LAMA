(define (domain Mio)
   (:requirements :strips :typing :adl)
   (:types Loc Agent NavMode ICam - Object
   )
   (:predicates
		 (modeTransition ?n1 - NavMode ?n2 - NavMode)
     (Navigation_Mode ?a - Agent ?n - NavMode)
		 (Communication_transmittedP ?p - Loc)
		 (RobotBase_NotOnDock ?a - Agent)
		 (RobotBase_OnDock ?a - Agent)
		 (RobotBase_At ?a - Agent ?p - Loc)
		 (Cameras_Picture ?a - Agent ?p - Loc)
		 (inside ?i - ICam ?a - Agent)
		 (visited ?p - Loc)
		 (dockPos ?p - Loc)
		 (free ?a - Agent)
   )

	 (:functions
		 (batperdis ?a - Agent ?n - NavMode)
     (distance_to_move ?p1 ?p2 - Loc)
		 (energyTransPhoto)
		 (photoEnergy)
		 (total-cost)
   )

   (:action RobotBase_GoingTo
     :parameters (?a - Agent ?n - NavMode ?p1 - Loc ?p - Loc)
     :precondition (and
			 						(Navigation_Mode ?a ?n)
									(RobotBase_NotOnDock ?a)
                	(RobotBase_At ?a ?p1)
                )
     :effect (and
			 					(not (RobotBase_At ?a ?p1))
								(visited ?p)
                (RobotBase_At ?a ?p)
								(increase (total-cost) (batperdis ?a ?n))
             )
   )

	 (:action Navigation_ChangeMode
		 :parameters (?a - Agent ?n1 - NavMode ?n2 - NavMode)
		 :precondition (and
			 (Navigation_Mode ?a ?n1)
			 (RobotBase_OnDock ?a)
			 (modeTransition ?n1 ?n2)
			 )
		 :effect (and
			 (not (Navigation_Mode ?a ?n1))
			 (Navigation_Mode ?a ?n2)
			 )
		)

		(:action Cameras_TakingPicture
			:parameters (?a - Agent ?p - Loc ?i - ICam)
			:precondition (and
								 (RobotBase_At ?a ?p)
								 (inside ?i ?a)
								 )
			:effect (and
								 (Cameras_Picture ?a ?p)
								 (increase (total-cost) (photoEnergy))
						     )
		)

		(:action Communication_TransmittingPicture
			:parameters (?a - Agent ?p - Loc)
			:precondition (and
								 (Cameras_Picture ?a ?p)
								 )
			:effect (and
								 (Communication_transmittedP ?p)
								 (increase (total-cost) (energyTransPhoto))
							)
	 )

		(:action RobotBase_Docking
      :parameters (?a - Agent ?p - Loc)
      :precondition (and
				         (dockPos ?p)
                 (RobotBase_At ?a ?p)
                 (RobotBase_NotOnDock ?a)
                 )
      :effect (and
								 (not (RobotBase_NotOnDock ?a))
                 (RobotBase_OnDock ?a)
                 )
    )

		(:action RobotBase_Undocking
			:parameters (?a - Agent ?p - Loc)
			:precondition (and
								 (dockPos ?p)
								 (RobotBase_At ?a ?p)
								 (RobotBase_OnDock ?a)
								 )
			:effect (and
								 (not (RobotBase_OnDock ?a))
								 (RobotBase_NotOnDock ?a)
								 )
		)
)
