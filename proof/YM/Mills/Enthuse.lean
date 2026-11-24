import YM.Mills.Spoors
/-! # Reviving Crew for any value norm Plant. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals Garden
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F j k:ℕ}{L:Side} {x u v a b c ν C D T θ w κ q Y ε e z η : ℝ} {i m:ℕ}{f g: ℝ→ℝ}
lemma enlarging {p c:Side}{J:Type}{S:Ratio p c}{G: Send S F J}{μ μ':J→ℝ}{t:ℝ} (h:Peak G x u v t μ)(hp: μ ≤ μ'): Peak G x u v t μ':= {h with spare := fun i U=> (h.spare i U).bumps (hp _) }
lemma rousing (L:Side)(F j k m l:ℕ)(u a p η ε t θ C K q:ℝ) (ht:θ<1/8)(hw:η<u)(hv:0<θ)(hx:1≤C)(hK:0<K): ∀ᶠ x in atTop, let Y:= fan L θ x; let B:=radiusB x
   ∀ {c f:Side}(J:Flight j k)(H:f.val=c.val*J.L.val)(δ b z:ℝ)(T:Grid f→Sheet f) (X:Sun J c f H δ b q u z l T),J.L=L→let V:=sliceL J H; let O:=X.equip F B; let μ i:=Real.exp 1*terra X F B Y (K*Y) i
   let μ':= tenderP X F B Y (K*Y) (lantern L x)
   Peak O (fiery su x L) Y (K*Y) C μ → reserve η (a+1) (conversion V m) ε→ reserve p (a+1) (conversion V m) t → highR L x ≤ 2*B→ ∀ {E D : Type}[Countable E][Countable D] (R:Rise f F E D)(Z:E→ℝ)(Q:D→ℝ)(W:Fj (Tr f) E D→Support c), Cents R Z Q Y (fiery su x L) → Fill R Z Q p p (taxK L x (7/8)) 1 (chipV L x) (highR L x)→ (∀ i,W i⊆ enlargement V m B (native O R i)) → Peak O (fiery su x L) Y (K*Y) C μ' ∧ Ready W B (paidSet O R μ' Z Q C 1 (taxK L x (1/2)) (lantern L x)) a (fundsL L θ x) 1 (1/2):=by
    filter_upwards [benefit (θ:=θ) L hx F,sponsorship L F m l θ u η K q (a+1) ε t ht hw hv, (Seat.shrinks (f:=chipV L) Seat.keeps (by norm_num) one_pos), Work.E01.radiusB_tendsto.eventually_ge_atTop (l+1)] with x h hg hχ he Y B c f J H δ b z T X hr V O μ μ' hX hd hP hB E D _ _ R Z Q W hZ hF hh
    have hz:=h.1; have hX':= enlarging hX (show μ ≤ μ' from fun i=>by unfold μ' tenderP; unfold μ; apply le_mul_of_one_le_right ((hX.spare i 1).nn); split; exact hz; exact le_rfl); have hb : 0<B:=by unfold B; omega
    have ht: 1≤ taxK L x (1/2):= Real.one_le_exp (mul_nonneg (by norm_num) (fan_pos ..).le)
    have hy:= paysV (η:=η) (ε:=ε) X F B m B (fun i=> W (.inl i)) (lantern L x) hz (fun i=> hh _) (show 0<Y from fan_pos ..) (mul_pos hK (show 0<Y from fan_pos ..)) hb (by unfold B; omega) hw.le hd; rw [hr] at hy
    let O':=fundsL L θ x; let τ := rust L θ x
    have hv':0 ≤ τ :=by unfold τ rust; positivity
    have hw':= honors (O:=O) hF (zero_le_one.trans hz) ht hx hZ hv' hh hb hB hP (fun i:D=>?_)
    -- z=lantern. trans' type weird. 
    swap
    · exact h.2 (R.front i).inv.card (card_pos.mpr (R.front i).alive)
    have hf:= Labels.together _ _ _ hy (Labels.together _ _ _ (hail hF zero_le_one hZ ((le_abs_self _).trans hχ) hh hb hB hP) hw')
    let tabs:=paidSet O R μ' Z Q C 1 (taxK L x (1/2)) (lantern L x)
    have hs : Ac.Hit W B tabs (a+1) (request L F m l θ u η K q (a+1) ε t x):=by
        have hl:V.count=L:=hr; -- W etc
        rw [hl] at hf -- occurs coercions?
        convert hf using 1 <;> try rfl
        all_goals funext i <;> rcases i with i|i|i <;> first|rfl|skip
        simp only [tabs,paidSet,Sum.elim_inr,one_mul]
    refine ⟨hX',hg.1,zero_lt_one,hg.2.2,(by norm_num),?_,fun i=>budget_loosen (hs i) hg.2.1⟩
    rintro (i|i|i)
    · exact (hX'.spare i 1).nn
    · exact mul_nonneg zero_le_one (sub_nonneg.mpr (Real.one_le_exp (hZ.pos i)))
    have hz:=zero_le_one.trans hz; exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (mul_nonneg hz (pow_nonneg (zero_le_one.trans ht) _))) (pow_nonneg (zero_le_one.trans hx) _)) (hZ.non _)
end YM.QCD.Jets.Touch
#print axioms YM.QCD.Jets.Touch.rousing
