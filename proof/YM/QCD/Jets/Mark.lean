import YM.QCD.Jets.Eve
/-! # separating hats & power weights. Supp arbitrary given x. DON'T shrink after. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{L:Side} {x u v a b c ν C D T θ: ℝ} {i j:ℕ}{f g: ℝ→ℝ}

lemma pale (a b:ℝ) (hb:b<a)(p:ℕ): Rate su L v (fun x=> Real.exp (-(a-b)*fossil (radiusB x) p)):=by
   let H:= -(a-b)/(4*(p:ℝ)+2); have hH : H < 0:=div_neg_of_neg_of_pos (by linarith) (by positivity)
   have hm:Rate su L v (fun x=> Real.exp (H*radiusB x)) :=by
     have he: Rate su L v (fun x=> Real.exp (-(-H)*Stores.till x)):=Rate.cutoff (neg_pos.mpr hH)
     refine he.compare (Eventually.of_forall fun x=> ?_)
     have hp:Stores.till x ≤ radiusB x:=Nat.div_le_self ..
     rw [neg_neg,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _),Real.exp_le_exp]; exact mul_le_mul_of_nonpos_left (by exact_mod_cast hp) hH.le
   have he:=hm.mul_right (Real.exp (H*(-2*p)))
   apply he.congr
   refine Eventually.of_forall fun x=>?_; dsimp only; rw [← Real.exp_add]; unfold fossil H; ring_nf

lemma expensed (F l t:ℕ):Seat L 0 (fun x=> (ballCost (l*radiusB x):ℝ)):=by
  simp only [ballCost,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_mul]; simpa only [zero_mul] using (Seat.powered (((Seat.radius (L:=L)|>.timesL (l:ℝ)).comb (Seat.radius.timesL (l:ℝ))).comb (Seat.numbers (1:ℝ))) 4)

lemma earned (l:ℕ)(w ξ:ℝ): Seat L 0 (fun x=> rem L l (radiusB x) w 1 ξ):=by
  unfold rem payment degreeIncome; simp only [Footprint.spread,extentCost,Nat.cast_mul]; -- see shape
  let C:=expensed (L:=L) 0 (l+20) 0
  exact (C.timesL _ |>.timesL _ |>.times _ |>.times _) -- check
lemma refunded (l:ℕ)(w γ:ℝ)(h:Seat L a g) : Seat L a (fun x=> rem L l (radiusB x) w (g x) γ):=by
   apply ((earned l w γ).ponies h |>.above (by linarith)).equal
   exact Eventually.of_forall fun i=> leeway ..

abbrev fan (L : Side)(θ x:ℝ):ℝ:=pra L x^θ
lemma fan_pos (L:Side)(θ x:ℝ) : 0< fan L θ x:=Real.rpow_pos_of_pos (Delay.monitor_pos ..) _
lemma skin_i (L:Side)(θ : ℝ): Seat L (-θ) (fun x=> (fan L θ x)⁻¹):= by
   apply Seat.keeps.equal; refine Eventually.of_forall (fun i=>?_); dsimp only [fan,pra]; rw [Real.rpow_neg (Delay.monitor_pos su L i).le]

lemma hide (L:Side)(F l mL:ℕ)(q C θ s u η ξ w:ℝ)(hu:η<u):
    Seat L (-θ*2) (fun x=>splitCost F (radiusB x) mL (radiusB x) l L q u η w ξ s (fan L θ x) (C*fan L θ x)):=by
    unfold splitCost
    have h:= (skin_i L θ).powered 2
    push_cast at h; refine Seat.comb ((h.timesL (fingers F^2)).ponies (refunded mL w ξ (Seat.numbers q))|>.above (by linarith)) ?_ -- numbers args
    have ht: Seat L (-θ*2) (fun x=> rem L mL (radiusB x) w (Real.exp (-(u-η)*fossil (radiusB x) l)*2*q) s):=refunded _ _ _ (((Seat.eliminated (a:=(-1:ℝ)) (pale _ _ hu _) (by norm_num)).times _).times _)
    apply (ht.timesL ((fingers F)^2*C)).equal
    exact Eventually.of_forall fun i=>by dsimp only; rw [mul_assoc C _ (fan L θ i)⁻¹, mul_inv_cancel₀ (fan_pos ..).ne', mul_one]
end YM.QCD.Jets.Touch
