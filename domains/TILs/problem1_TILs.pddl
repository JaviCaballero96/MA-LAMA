; The template is used for the multiple boxes load.

(define (problem  miptool_plus_problem)
(:domain miptool_plus_domain)

(:objects
    stringd_box1 stringd_box2  - box_stringd
    foxizirc robin  - robot
    stringd_labpol   stringd_pad    stringd_opsm     stringd_pebd stringd_pp3    stringd_compuestos  - placeid_stringd

)
(:init

    (robot_at foxizirc stringd_labpol )
    (available foxizirc )
    (= (capacity_left foxizirc) 45)
    (= (robot_speed foxizirc) 250)
    (visited_place foxizirc stringd_labpol )
    (= (operation_time foxizirc) 3)


    (robot_at robin stringd_labpol )
    (available robin )
    (= (capacity_left robin) 50)
    (= (robot_speed robin) 250)
    (visited_place robin stringd_labpol )
    (= (operation_time robin) 3)



    (= (manip_objects_time) 3)



    (at 240.0 (box_at stringd_box1 stringd_pad))
    (at 270.0 (not (on_time stringd_box1)))
    (on_time stringd_box1)
    (associated_lab stringd_box1 stringd_labpol)
    (= (weight stringd_box1) 20)

    (at 240.0 (box_at stringd_box2 stringd_pp3))
    (at 270.0 (not (on_time stringd_box2)))
    (on_time stringd_box2)
    (associated_lab stringd_box2 stringd_labpol)
    (= (weight stringd_box2) 20)


    (is_lab stringd_labpol)
    (is_lab stringd_labinter)


    (= (distance stringd_opsm stringd_pad) 260)
    (= (distance stringd_pad stringd_opsm) 260)
    (valid_path stringd_opsm stringd_pad)
    (valid_path stringd_pad stringd_opsm)

    (= (distance stringd_pebd stringd_labpol) 40)
    (= (distance stringd_labpol stringd_pebd) 40)
    (valid_path stringd_pebd stringd_labpol)
    (valid_path stringd_labpol stringd_pebd)

    (= (distance stringd_pp3 stringd_compuestos) 275)
    (= (distance stringd_compuestos stringd_pp3) 275)
    (valid_path stringd_pp3 stringd_compuestos)
    (valid_path stringd_compuestos stringd_pp3)

    (= (distance stringd_compuestos stringd_pebd) 80)
    (= (distance stringd_pebd stringd_compuestos) 80)
    (valid_path stringd_compuestos stringd_pebd)
    (valid_path stringd_pebd stringd_compuestos)

    (= (distance stringd_opsm stringd_pebd) 2000)
    (= (distance stringd_pebd stringd_opsm) 2000)
    (valid_path stringd_opsm stringd_pebd)
    (valid_path stringd_pebd stringd_opsm)




)
(:goal (and

    (collected stringd_box1)

    (collected stringd_box2)


))

(:metric minimize (total-time))

)
