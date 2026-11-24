import YM.QCD.Jets.Purse
/-! # receipt renewal uses same-lattice input-budget. Doors include overlap. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F j k:ℕ}{L:Side} {x u v a b c ν C D T θ w κ q Y ε e z: ℝ} {i m:ℕ}{f g: ℝ→ℝ}

-- a+i shells on old and input. expensive distortion in output footprints.

def highR (L:Side)(x:ℝ):ℕ:=radiusB (betaF su x L)

def ask (L:Side)(mL:ℕ)(θ w ε :ℝ)(x:ℝ):ℝ:= (cashM L θ x*Real.exp 1*rem L mL (radiusB x) w (chip L x) ε+rust L θ x*rem L mL (radiusB x) w 1 ε)
lemma cashOut (L:Side)(mL:ℕ)(θ w ε:ℝ) : Seat L (-2*θ) (ask L mL θ w ε):=by
   let Q : ℝ→ℝ:=fun x=> rust L θ x * rem L mL (radiusB x) w 1 ε
   have hp: Seat L (-2*θ) Q:=(chip_r L θ|>.ponies (earned mL w ε)).above (by linarith)
   apply ((hp.times (Real.exp 1)).comb hp).equal
   filter_upwards [Delay.shift_pos su L] with x hx
   have hz:=healthy_chip hx; dsimp only [Q,ask]; unfold cashM; rw [leeway L]; field_simp at *

abbrev ramp (L:Side)(F m b:ℕ)(a C θ:ℝ)(ρ q η ε ξ:ℝ)(x:ℝ):=splitCost F (radiusB x) m (radiusB x) b L q ρ η a ε ξ (fan L θ x) (C*fan L θ x)

lemma readyW (L:Side)(C a θ v q u w y η ε ξ:ℝ)(F mL b:ℕ)(hh:0<θ)(hw:η<u) :
    let R:=ramp L F mL b a C θ u q η ε ξ; ∀ᶠ x in atTop,
      let d:=radiusB x; let γ:= fan L (-θ-θ/2) x; let δ := fan L (-θ) x
      R x≤1 ∧ Real.exp 1 * R x + ask L mL θ a w x ≤ γ ∧ degreePrice d γ 1≤ δ ∧ δ < 1 := by
   intro R; have hR:Seat L (-2*θ) R:=(hide L F b mL q C θ ξ u η ε a hw).above (by linarith)
   have he:Seat L (-2*θ) (fun x=> Real.exp 1*R x + ask L mL θ a w x):=(hR.timesL _).comb (cashOut L mL θ a w)
   have hk:Seat L (-θ-θ/2) (fun x=> degreePrice (radiusB x) (fan L (-θ-θ/2) x) 1):=by
      have hm: Seat L 0 (fun x=> (ballCost (radiusB x):ℝ)):=by simpa only [one_mul] using expensed (L:=L) 0 1 0
      unfold degreePrice stretch; simp only [div_one]; exact (hm.ponies Seat.keeps |>.timesL 4 |>.above (by linarith))
   filter_upwards [hR.shrinks (by linarith) (show (0:ℝ)<1 from zero_lt_one), he (-θ-θ/2) (by linarith),hk (-θ) (by linarith),Seat.keeps (L:=L) (a:=-θ)|>.shrinks (by linarith) (D:=1/2) (by norm_num)] with x h g H hx
   dsimp only; exact ⟨(le_abs_self _).trans h,(le_abs_self _).trans g,(le_abs_self _).trans H, ((le_abs_self _).trans hx).trans_lt (by norm_num)⟩

lemma lets (L:Side)(θ:ℝ)(hh:0<θ)(u v a:ℝ)(hs:0<u)(K C:ℝ)(hK:0<K)(hC:1≤C)(a' w η q ρ ε ξ:ℝ)(hz:η<ρ)(F j k mL b:ℕ)(hw:0≤a)(hy:2*w<u)(he:0<w) : ∀ᶠ x:ℝ in atTop,
    ∀ (c f: Side)(G:Flight j k)(T:Grid f→Sheet f)(hL:G.L=L) (H:f.val=c.val*G.L.val) (v δ μ:ℝ) (P:Sun G c f H δ v q ρ μ b T)(π:ℝ),
    let S:= sliceL G H; let o:=P.equip F (radiusB x); let m i:= Real.exp 1*terra P F (radiusB x) (fan L θ x) (K*fan L θ x) i
    reserve u (a+1) (conversion S mL) w → reserve ρ (a+1) (conversion S mL) ε → reserve η (a+1) (conversion S mL) ξ→ Fork.Sea G H (radiusB x) δ π q (fiery su x L) P.Z P.V 0 → K*fingers F*π ≤1 → K*fingers F*q ≤ C →
    ∀ {E J : Type} [Countable E] [Countable J],∀ (R:Rise f F E J)(β:E→ℝ)(Q:J→ℝ)(W:Cove.Fj (Tr f) E J→Support c), Cents R β Q (fan L θ x) (fiery su x L) → Fill R β Q u u (taxK L x 1) 1 (chip L x) (highR L x)→ Cove.Count o R W → (∀ i,W i⊆ enlargement S mL (radiusB x) (native o R i)) →
    let γ:= fan L (-θ-θ/2) x; let p:=fan L (-θ) x
    (Peak o (fiery su x L) (fan L θ x) (K*fan L θ x) C m) ∧ 1 ≤ cashM L θ x ∧ 1≤taxK L x (1/2) ∧ Ready W (radiusB x) (paidSet o R m β Q C (cashM L θ x) (taxK L x (1/2)) 1) a γ 1 p:=by
  filter_upwards [readyW L K (a+1) θ v q ρ w u η ε ξ F mL b hh hz,event_chip L θ,toll L θ F C (by linarith), Work.E01.radiusB_tendsto.eventually_ge_atTop b, Fees.horizons su L mL he hw hy] with x hx h hp hB hw c f G T hL H v δ μ P π S O m hr ht he ha hy hd E J _ _ R β Q W hC' hK' HH hm
  let Y i:=W (.inl i)
  have hl:S.count=L:=hL; have heY i: (roomK i).image S.parent ⊆ Y i:=by
    intro j hj; apply HH.budget (.inl i); apply image_subset_image (halo_subset _ _) hj -- arguments
  have hX : Sea G H (radiusB x) δ π q (fiery su x L) P.Z P.V 0:=ha
  have hx₁:=fan_pos L θ x
  let w:=fan L θ x; let B0:=radiusB x
  obtain ⟨hj,hY⟩:= P.paysAll F B0 B0 mL π C 0 0 Y (fun i=> hm _) hx₁ (mul_pos hK hx₁) hw.1 (by omega) hz.le he ht heY ha hC (show K*w*fingers F*π ≤ w from calc _ = K*fingers F*π*w:=by ring
                                                                                                                                                                      _ ≤ _:=mul_le_of_le_one_left hx₁.le hy) (show K*w*fingers F*q≤C*w by calc _ =K*fingers F*q*w:=by ring
                                                                                                                                                                                                                                               _ ≤_:=mul_le_mul_of_nonneg_right hd hx₁.le) (by rw [hL]; exact hx.1)
  have hν:1≤ taxK L x (1/2):= Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le)
  have hh:=award hK' hj hC' hY (zero_le_one.trans h.2.2.2) hν h.2.2.1 (show 0≤ rust L θ x by unfold rust; positivity) hm hw.1 hw.2.1 hr (fun i=> hp _ (Finset.card_pos.mpr (R.front i).alive))
  rw [hL,hl] at hh -- dependent risk
  refine ⟨hj,h.2.2.2,hν,fan_pos ..,zero_lt_one,hx.2.2.1,hx.2.2.2,fun i=> ?_,fun i=>budget_loosen (hh i) hx.2.1⟩
  cases i with
  | inl i=>exact (hj.spare i 1).nn
  | inr i=>
   unfold paidSet; cases i with
   | inl i=> exact mul_nonneg (zero_le_one.trans h.2.2.2) (sub_nonneg.mpr (Real.one_le_exp (hC'.pos i)))
   | inr i=> exact mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans h.2.2.2) (by have h:=zero_lt_one.trans_le hν; positivity)) (by have h:=zero_lt_one.trans_le hC; positivity)) (hC'.non i)
end YM.QCD.Jets.Touch
