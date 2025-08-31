; The template is used for the multiple boxes load.

(define (problem  miptool_plus_problem)
(:domain miptool_plus_domain)

(:objects 
    stringd_box1 stringd_box2 stringd_box3 stringd_box4 stringd_box5 stringd_box6 stringd_box7 stringd_box8 stringd_box9 stringd_box10 stringd_box11 stringd_box12 stringd_box13 stringd_box14 stringd_box15  - box_stringd 
    foxizirc robin  - robot 
    stringd_labpol stringd_labinter stringd_almopsm stringd_pad stringd_ec stringd_glic  stringd_opsm  stringd_pp2  stringd_pflex stringd_pebd stringd_pp3  stringd_ppolm stringd_cog1 stringd_compuestos  - placeid_stringd 

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


    
    (at 420.0 (box_at stringd_box1 stringd_opsm))
    (at 480.0 (not (on_time stringd_box1)))
    (on_time stringd_box1)
    (associated_lab stringd_box1 stringd_labinter)
    (= (weight stringd_box1) 20)
    
    (at 420.0 (box_at stringd_box2 stringd_opsm))
    (at 480.0 (not (on_time stringd_box2)))
    (on_time stringd_box2)
    (associated_lab stringd_box2 stringd_labinter)
    (= (weight stringd_box2) 20)
    
    (at 420.0 (box_at stringd_box3 stringd_almopsm))
    (at 480.0 (not (on_time stringd_box3)))
    (on_time stringd_box3)
    (associated_lab stringd_box3 stringd_labinter)
    (= (weight stringd_box3) 20)
    
    (at 420.0 (box_at stringd_box4 stringd_pflex))
    (at 480.0 (not (on_time stringd_box4)))
    (on_time stringd_box4)
    (associated_lab stringd_box4 stringd_labinter)
    (= (weight stringd_box4) 20)
    
    (at 420.0 (box_at stringd_box5 stringd_pflex))
    (at 480.0 (not (on_time stringd_box5)))
    (on_time stringd_box5)
    (associated_lab stringd_box5 stringd_labinter)
    (= (weight stringd_box5) 20)
    
    (at 420.0 (box_at stringd_box6 stringd_ppolm))
    (at 480.0 (not (on_time stringd_box6)))
    (on_time stringd_box6)
    (associated_lab stringd_box6 stringd_labinter)
    (= (weight stringd_box6) 20)
    
    (at 420.0 (box_at stringd_box7 stringd_ppolm))
    (at 480.0 (not (on_time stringd_box7)))
    (on_time stringd_box7)
    (associated_lab stringd_box7 stringd_labinter)
    (= (weight stringd_box7) 20)
    
    (at 420.0 (box_at stringd_box8 stringd_ec))
    (at 450.0 (not (on_time stringd_box8)))
    (on_time stringd_box8)
    (associated_lab stringd_box8 stringd_labinter)
    (= (weight stringd_box8) 20)
    
    (at 420.0 (box_at stringd_box9 stringd_ec))
    (at 450.0 (not (on_time stringd_box9)))
    (on_time stringd_box9)
    (associated_lab stringd_box9 stringd_labinter)
    (= (weight stringd_box9) 20)
    
    (at 450.0 (box_at stringd_box10 stringd_ec))
    (at 480.0 (not (on_time stringd_box10)))
    (on_time stringd_box10)
    (associated_lab stringd_box10 stringd_labinter)
    (= (weight stringd_box10) 20)
    
    (at 450.0 (box_at stringd_box11 stringd_ec))
    (at 480.0 (not (on_time stringd_box11)))
    (on_time stringd_box11)
    (associated_lab stringd_box11 stringd_labinter)
    (= (weight stringd_box11) 20)
    
    (at 420.0 (box_at stringd_box12 stringd_pad))
    (at 450.0 (not (on_time stringd_box12)))
    (on_time stringd_box12)
    (associated_lab stringd_box12 stringd_labpol)
    (= (weight stringd_box12) 20)
    
    (at 420.0 (box_at stringd_box13 stringd_compuestos))
    (at 450.0 (not (on_time stringd_box13)))
    (on_time stringd_box13)
    (associated_lab stringd_box13 stringd_labpol)
    (= (weight stringd_box13) 20)
    
    (at 420.0 (box_at stringd_box14 stringd_pp2))
    (at 450.0 (not (on_time stringd_box14)))
    (on_time stringd_box14)
    (associated_lab stringd_box14 stringd_labpol)
    (= (weight stringd_box14) 20)
    
    (at 420.0 (box_at stringd_box15 stringd_pebd))
    (at 450.0 (not (on_time stringd_box15)))
    (on_time stringd_box15)
    (associated_lab stringd_box15 stringd_labpol)
    (= (weight stringd_box15) 20)
    

    (is_lab stringd_labpol)
    (is_lab stringd_labinter)

       
    (= (distance stringd_ppolm stringd_cog1) 200)
    (= (distance stringd_cog1 stringd_ppolm) 200)
    (valid_path stringd_ppolm stringd_cog1)
    (valid_path stringd_cog1 stringd_ppolm)
     
    (= (distance stringd_pflex stringd_cog1) 470)
    (= (distance stringd_cog1 stringd_pflex) 470)
    (valid_path stringd_pflex stringd_cog1)
    (valid_path stringd_cog1 stringd_pflex)
     
    (= (distance stringd_ec stringd_cog1) 950)
    (= (distance stringd_cog1 stringd_ec) 950)
    (valid_path stringd_ec stringd_cog1)
    (valid_path stringd_cog1 stringd_ec)
     
    (= (distance stringd_glic stringd_cog1) 500)
    (= (distance stringd_cog1 stringd_glic) 500)
    (valid_path stringd_glic stringd_cog1)
    (valid_path stringd_cog1 stringd_glic)
     
    (= (distance stringd_glic stringd_almopsm) 25)
    (= (distance stringd_almopsm stringd_glic) 25)
    (valid_path stringd_glic stringd_almopsm)
    (valid_path stringd_almopsm stringd_glic)
     
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
      
    (= (distance stringd_ppolm stringd_pebd) 1500)
    (= (distance stringd_pebd stringd_ppolm) 1500)
    (valid_path stringd_ppolm stringd_pebd)
    (valid_path stringd_pebd stringd_ppolm)
     
    (= (distance stringd_pflex stringd_pebd) 1100)
    (= (distance stringd_pebd stringd_pflex) 1100)
    (valid_path stringd_pflex stringd_pebd)
    (valid_path stringd_pebd stringd_pflex)
     
    (= (distance stringd_ec stringd_pebd) 1050)
    (= (distance stringd_pebd stringd_ec) 1050)
    (valid_path stringd_ec stringd_pebd)
    (valid_path stringd_pebd stringd_ec)
      
    (= (distance stringd_glic stringd_pebd) 1600)
    (= (distance stringd_pebd stringd_glic) 1600)
    (valid_path stringd_glic stringd_pebd)
    (valid_path stringd_pebd stringd_glic)
     
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
     
    (collected stringd_box9)
     
    (collected stringd_box10)
     
    (collected stringd_box11)
     
    (collected stringd_box12)
     
    (collected stringd_box13)
     
    (collected stringd_box14)
     
    (collected stringd_box15)
    

))

(:metric minimize (total-time))

)
