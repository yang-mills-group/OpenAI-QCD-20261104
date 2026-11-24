import YM.Needle.Mind
/-!
  One underlying basis. Bound the genuine insertion of ANY point label, not separate
  coincident reals at each precision. Stock rays and diminishing envelopes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) (Ht:SourceRead.TaperHol){Go:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Go)(sym:RawSym)(base:ℕ→ℕ) (U:Massive.Lining.Temper.Collage.Exhibit.CoreMix)
local notation "S"=> C.S
local notation "Q"=> Uv.display C Ht sym U base
variable {d:ℕ}(hX:(Uv.display C Ht sym U base).System)
variable (hY:Spent C (Uv.display C Ht sym U base))
variable (e:ℝ)(he:0<e)
variable (hs:Sway C.S){β ν:ℝ}(hC:C.Path β ν)
include hX hY hs hC he
lemma golden (w:Label d) : ∃ v:ℝ,0≤ v∧∀ᶠ j in atTop,∀ᶠ i in atTop, GreenP C i j (stem Q d i w) (Hub.rayM C.S d e v j):=by
   have hh(p:Bool): let t:= facing sym p w; ∃ v:ℝ,0≤ v∧∀ᶠ j in atTop,∀ᶠ i in atTop, GreenP C i j (stem Q d i t) (Hub.rayM C.S d e v j):=by
      intro t; by_cases h:t=0; · rw [h]; refine ⟨0,le_rfl,Eventually.of_forall fun i=> Eventually.of_forall fun j=>?_⟩; rw [map_zero,Hub.rayM,zero_mul]; exact GreenP.zero
      obtain ⟨v,hv,h⟩:= Hub.starlight Ht Uv sym base U t p (fronting ..) h hX hY e he hs hC; exact ⟨v,hv,h.mono fun i h=> h.mono fun j h=> GreenP.leaf Q d h⟩
   obtain ⟨v,hv,H⟩:= hh true; obtain ⟨c,hc,G⟩:= hh false; refine ⟨v+c,add_nonneg hv hc,?_⟩
   filter_upwards [H,G] with j hj h; filter_upwards [hj,h] with i hi hv
   rw [revelation sym w, map_add, Hub.rayM, add_mul]; exact GreenP.add hi hv
structure Capital (P:Calibration C) (d:ℕ) (e:ℝ) where
    v:ℝ
    green:0 ≤ v
    nest: ∀ᶠ j in atTop,∀ᶠ i in atTop,∀ q: Label d,GreenP C i j (stem P d i q) (‖q‖*Hub.rayM C.S d e v j)
lemma backed (d:ℕ): Nonempty (Capital Q d e):=by
    let b:= Module.finBasis ℂ (Label d); let Γ:= Fin (Module.finrank ℂ (Label d)); choose v hv h using fun i:Γ=> golden Ht Uv sym base U hX hY e he hs hC (b i)
    let F (i:Γ):= (b.coord i).toContinuousLinearMap; let V:=∑ i:Γ,‖F i‖ * v i
    have hp : 0≤V:= Finset.sum_nonneg fun i _=> mul_nonneg (norm_nonneg _) (hv i)
    refine ⟨V,hp,?_⟩; filter_upwards [eventually_all.mpr h] with j hJ; filter_upwards [eventually_all.mpr hJ] with i hi w
    have hx:w=∑ k:Γ,F k w • b k :=(b.sum_repr w).symm
    have ht := GreenP.sum univ (fun i' :Γ=> F i' w • stem Q d i (b i')) (fun i'=> ‖F i' w‖*Hub.rayM C.S d e (v i') j) (fun k _=> GreenP.smul (hi k) _); refine GreenP.mono (k:=∑ k:Γ, ‖F k w‖ *Hub.rayM C.S d e (v k) j) (x:=(stem Q d i) w) ?_ ?_
    · conv => arg 4; rw [hx]
      rw [map_sum]; simp_rw[map_smul]; exact ht
    unfold Hub.rayM V; rw [Finset.sum_mul,Finset.mul_sum]; refine sum_le_sum (fun k _=>?_)
    have hh : 0 ≤ v k * Real.exp (((d:ℝ)/2+e)* Hub.clock C.S j):=mul_nonneg (hv _) (Real.exp_nonneg _)
    exact ((mul_le_mul_of_nonneg_right ((F k).le_opNorm _) hh)).trans_eq (by ring)
omit hX hY hs hC he
namespace Capital
variable {P e}(K:Capital P d e)
lemma power (j:ℕ):0 ≤ rayM C.S d e K.v j:= mul_nonneg K.green (Real.exp_nonneg _)
lemma gains {v:ℝ}:∀ᶠ j in atTop,∀ᶠ i in atTop,∀ x:Label d, ‖x‖≤v → GreenP C i j (stem P d i x) (v*Hub.rayM C.S d e K.v j):= K.nest.mono fun j h=> h.mono fun i h x hi=> (GreenP.mono (h x) (mul_le_mul_of_nonneg_right hi (K.power _)))
end Capital
namespace Investment
variable {P}(K:Invest P d)
noncomputable abbrev face (i:ℕ):(Fin (deficit d)→ℂ)→ₗ[ℂ]Label d where
   toFun f:=∑ j,f j • K.bonds i j
   map_add' a b:=by simp only [Pi.add_apply,add_smul,sum_add_distrib]
   map_smul' a b:=by simp only [Pi.smul_apply,smul_eq_mul,smul_sum,smul_smul,RingHom.id_apply]
set_option maxHeartbeats 300000 in
lemma creditW: ∀ᶠ j in atTop,∃ f: ℕ→ℝ,Tendsto (fun i=>K.scale i*f i) atTop (𝓝 0)∧ ∀ᶠ i in atTop, 0 ≤ f i∧ ∀ a:Fin (deficit d)→ ℂ, GreenP C i j (stem P d i (face K i a)) (‖a‖*f i):=by
    filter_upwards [eventually_all.mpr (fun i: Fin (deficit d)=> K.race i)] with j h; let F(i:ℕ):=∑ k:Fin (deficit d), K.bud k j i
    refine ⟨F,?_,?_⟩
    · have hh:= tendsto_finsetSum univ (fun k :Fin (deficit d)=> fun _=>(h k).1); simpa [F,mul_sum] using hh
    filter_upwards [eventually_all.mpr (fun i:Fin (deficit d)=> (h i).2)] with i hv
    refine ⟨(Finset.sum_nonneg fun a _=> (hv a).2),fun p=>?_⟩; change GreenP _ _ _ (stem P d i (∑ k,p k • K.bonds i k)) _; rw [map_sum]; simp_rw [map_smul]; unfold F; rw [mul_sum]; apply GreenP.sum; intro k _; exact GreenP.mono (GreenP.smul (GreenP.leaf P d (hv k).1) (p k)) (mul_le_mul_of_nonneg_right (norm_le_pi_norm p k) (hv k).2)
end Investment
end YM.Massive.Needle
#print axioms YM.Massive.Needle.backed
#print axioms YM.Massive.Needle.Investment.creditW
