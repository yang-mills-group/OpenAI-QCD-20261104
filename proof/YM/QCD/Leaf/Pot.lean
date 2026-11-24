import YM.QCD.Leaf.Rich
import YM.QCD.Garden.Temple

/-! # Ward unaffected by real saturation. relative to sheet coordinates and chart
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.LeafM
open Lat Function Lattice Wilson Kit Cost Run Rudder Finset RG Eyrie Stationary Sparks Revolve Paths Quarry Orbit Garden
open Filter Metric
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical Asymptotics
variable {n: Side}{I:Type}{k B:ℕ}{C:I→Bloom k}{σ t η δ c p ξ:ℝ}
lemma plankU (W:Slot)(x:Site n):ContDiffAt ℝ ω (fun B=> W.atSite (input su n B) x) 0:=by
  have hx (i : su.ColorIndex) : ContDiff ℂ ω (fun P=>leafC (n:=n) W x P i):=contDiff_iff_contDiffAt.mpr fun i'=> (PolyDisc.finiteD _ (Eventually.of_forall (growing W x i))).contDiffAt
  let Y:=fun B=> W.atSite (input su n B) x
  refine ?_
  let L:= (PiLp.continuousLinearEquiv 2 ℝ (fun _ : su.ColorIndex=> ℝ))
  have hg : ContDiffAt ℝ ω (L∘ Y) 0:=by
    apply contDiffAt_pi.2; intro i; change ContDiffAt ℝ ω (fun b=> ((Y b) i)) _; have hm B: Y B i=(leafC W x (settled (input su n B)) i).re:= by rw [pinning]; rfl
    simp_rw [hm]; exact (Complex.reCLM.contDiff.comp (((hx i).restrict_scalars ℝ).comp (pulse_flow n))).contDiffAt
  convert L.symm.contDiff.contDiffAt.comp _ hg using 1; ext1 i; exact (L.symm_apply_apply ..).symm
lemma terrain (a:Cnr n):∃ d:ℝ,0<d ∧ ∀ᶠ r:ℝ in cutRay, meek (input su n (r • a)) (d*|r|) :=by
  let F (r:ℝ):= fun i: Face (Per n)=> Slot.atSite ⟨[],i.2⟩ (input su n (r • a)) i.1
  have hh : ContDiffAt ℝ ω F (0:ℝ) := by
    apply contDiffAt_pi.2; intro i; let g x:= Slot.atSite ⟨[],i.2⟩ (input su n x) i.1; refine ContDiffAt.comp (g:=g) (f:=fun t:ℝ=> t • a) (n:=ω) (𝕜:=ℝ) (0:ℝ) ?_ ?_
    · rw [zero_smul]; exact plankU _ _
    all_goals first | rfl | fun_prop
  have hx:F 0=0:=by funext i; unfold F; rw [zero_smul,input_zero]; exact Bloom.slot_tail ..
  have hm: (fun i=>F i - F 0)=O[𝓝 (0:ℝ)] (fun i=> i-0):= (hh.differentiableAt (by simp)).isBigO_sub; rw [hx] at hm; simp only [sub_zero] at hm
  obtain ⟨d,hd,h⟩:=hm.exists_pos
  refine ⟨d,hd,h.bound.filter_mono nhdsWithin_le_nhds |>.mono fun r ht W x => ?_⟩
  let V: Slot:=⟨[],W.plaq⟩; have he: ‖W.atSite (input su n (r • a)) x‖=‖F r (qmark W x,W.plaq)‖:=by
    change _=‖V.atSite (input su n _) (qmark W x)‖; unfold Slot.atSite Slot.eval; rw [Gauge.norm_adjoint,Gauge.norm_adjoint]; unfold faceValue; rw [travel_at,travel_at]; simp [V,Slot.offset,qmark,stop]
  rw [he]; exact (norm_le_pi_norm _ _).trans ht

lemma buds (C:I→Bloom k) (hp:0<ξ)(ht:ξ≤1)(h: Fractal C σ p)(hs:0 < σ): Tender (castF (wild C ξ n)) (castF (dust C n)) (k+2):=by
  obtain ⟨δ,w,B,hD,hw,H⟩ := rich k hs (t:=0) le_rfl
  have hh := estate (H I C p h ξ hp ht n B le_rfl) (by positivity)
  have hη := serenity (n:=n) h hs
  refine ⟨rays_nil ((hh.sub hη).analyticAt) (k:=k+1) (fun a=> ?_),hh,hη⟩
  obtain ⟨d,hy,hu⟩:= terrain a
  let D:= p*k/ξ^2*d^(k+2)
  have hm : Tendsto (fun r:ℝ=>D*‖r‖) cutRay (𝓝 0):=by simpa only [norm_zero,mul_zero] using ((continuous_norm.continuousAt (x:=(0:ℝ))).tendsto.const_mul D).mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))
  refine squeeze_zero_norm' ?_ hm
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:={0}ᶜ),hu] with r hr hX
  have hr : r ≠ 0:=hr
  rw [norm_smul,norm_inv,norm_pow,Real.norm_eq_abs]
  refine le_trans (mul_le_mul_of_nonneg_left (lodge _ h hs hX hp ht (by positivity)) (by positivity)) ?_
  unfold D; apply le_of_eq; rw [show k+2=k+1+1 from rfl,mul_pow d,pow_succ (abs r)]; field_simp; ring
lemma presentation (C:I→Bloom k) (hv: Orbit.Birth.Vital (dust C))(hp: Fractal C σ p): dust (frosting C) n=dust C n:=by
  rw [coined_inv hp]; have ht:= hv.1 n|>.2.1; let A:=dust C n; have hx s v : inverted A s v=A v:=by
    unfold inverted A; rw [ht.port v s (fun x=>_) (starTraffic _) (gems _ _) (fleetLeft _)]; exact Orbit.compatible _ _ (colour_wheel (gems ..) (fleetLeft s))
  funext U; rw [occult]; rw [show hearth (dust C n) U=A U from ?_]; rw [← ht.lane U]; module -- maybe
  unfold hearth; change ((Fintype.card Signed:ℝ)⁻¹) • ∑ s:Signed,inverted A s U=A U; simp_rw [hx]; rw [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_pos.ne'),one_smul]
end YM.QCD.Leaf.LeafM
