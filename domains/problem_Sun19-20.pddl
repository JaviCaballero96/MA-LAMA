; The template is used for the multiple boxes load.

(define (problem  miptool_plus_problem)
(:domain miptool_plus_domain)

(:objects 
    stringd_box1 stringd_box2 stringd_box3 stringd_box4 stringd_box5 stringd_box6 stringd_box7 stringd_box8  - box_stringd 
    foxizirc robin  - robot 
    stringd_labpol stringd_labinter  stringd_pad stringd_ec   stringd_opsm  stringd_pp2   stringd_pebd stringd_pp3   stringd_cog1 stringd_compuestos  - placeid_stringd 

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


    
    (at 1140.0 (box_at stringd_box1 stringd_ec))
    (at 1170.0 (not (on_time stringd_box1)))
    (on_time stringd_box1)
    (associated_lab stringd_box1 stringd_labinter)
    (= (weight stringd_box1) 20)
    
    (at 1140.0 (box_at stringd_box2 stringd_ec))
    (at 1170.0 (not (on_time stringd_box2)))
    (on_time stringd_box2)
    (associated_lab stringd_box2 stringd_labinter)
    (= (weight stringd_box2) 20)
    
    (at 1170.0 (box_at stringd_box3 stringd_ec))
    (at 1200.0 (not (on_time stringd_box3)))
    (on_time stringd_box3)
    (associated_lab stringd_box3 stringd_labinter)
    (= (weight stringd_box3) 20)
    
    (at 1170.0 (box_at stringd_box4 stringd_ec))
    (at 1200.0 (not (on_time stringd_box4)))
    (on_time stringd_box4)
    (associated_lab stringd_box4 stringd_labinter)
    (= (weight stringd_box4) 20)
    
    (at 1140.0 (box_at stringd_box5 stringd_pad))
    (at 1170.0 (not (on_time stringd_box5)))
    (on_time stringd_box5)
    (associated_lab stringd_box5 stringd_labpol)
    (= (weight stringd_box5) 20)
    
    (at 1140.0 (box_at stringd_box6 stringd_compuestos))
    (at 1170.0 (not (on_time stringd_box6)))
    (on_time stringd_box6)
    (associated_lab stringd_box6 stringd_labpol)
    (= (weight stringd_box6) 20)
    
    (at 1140.0 (box_at stringd_box7 stringd_pp2))
    (at 1170.0 (not (on_time stringd_box7)))
    (on_time stringd_box7)
    (associated_lab stringd_box7 stringd_labpol)
    (= (weight stringd_box7) 20)
    
    (at 1140.0 (box_at stringd_box8 stringd_pebd))
    (at 1170.0 (not (on_time stringd_box8)))
    (on_time stringd_box8)
    (associated_lab stringd_box8 stringd_labpol)
    (= (weight stringd_box8) 20)
    

    (is_lab stringd_labpol)
    (is_lab stringd_labinter)

         
    (= (distance stringd_ec stringd_cog1) 950)
    (= (distance stringd_cog1 stringd_ec) 950)
    (valid_path stringd_ec stringd_cog1)
    (valid_path stringd_cog1 stringd_ec)
       
    (= (distance stringd_opsm stringd_cog1) 830)
    (= (distance stringd_cog1 stringd_opsm) 830)
    (valid_path stringd_opsm stringd_cog1)
    (valid_path stringd_cog1 stringd_opsm)
     
    (= (distance stringd_opsm stringd_pad) 260)
    (= (distance stringd_pad stringd_opsm) 260)
    (valid_path stringd_opsm stringd_pad)
    (valid_path stringd_pad stringd_opsm)
        
    (= (distance stringd_pebd stringd_cog1) 1500)
    (= (distance stringd_cog1 stringd_pebd) 1500)
    (valid_path stringd_pebd stringd_cog1)
    (valid_path stringd_cog1 stringd_pebd)
     
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
     
    (= (distance stringd_pp2 stringd_pp3) 180)
    (= (distance stringd_pp3 stringd_pp2) 180)
    (valid_path stringd_pp2 stringd_pp3)
    (valid_path stringd_pp3 stringd_pp2)
        
    (= (distance stringd_ec stringd_pebd) 1050)
    (= (distance stringd_pebd stringd_ec) 1050)
    (valid_path stringd_ec stringd_pebd)
    (valid_path stringd_pebd stringd_ec)
       
    (= (distance stringd_opsm stringd_pebd) 2000)
    (= (distance stringd_pebd stringd_opsm) 2000)
    (valid_path stringd_opsm stringd_pebd)
    (valid_path stringd_pebd stringd_opsm)
       
    (= (distance stringd_cog1 stringd_labinter) 35)
    (= (distance stringd_labinter stringd_cog1) 35)
    (valid_path stringd_cog1 stringd_labinter)
    (valid_path stringd_labinter stringd_cog1)
    

    

)
(:goal (and 
     
    (collected stringd_box1)
     
    (collected stringd_box2)
     
    (collected stringd_box3)
     
    (collected stringd_box4)
     
    (collected stringd_box5)
     
    (collected stringd_box6)
     
    (collected stringd_box7)
     
    (collected stringd_box8)
    

))

(:metric minimize (total-time))

)