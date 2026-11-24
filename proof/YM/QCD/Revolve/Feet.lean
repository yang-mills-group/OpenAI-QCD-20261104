import YM.QCD.Revolve.Fusion

/-! # budget control at fixed width for inherited corrections -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lat Function Lattice Wilson Kit Pine Cost Eyrie Quarry Rudder RG Finset Filter Stationary Sparks
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {n : Side}{k : ℕ}{I J: Type}{P : I→Bloom k}{V : J→ Bloom k}{r t u b C:ℝ}
variable {W:LegInk n}{B F:trackG n}
lemma donate (h:Noble F)(he:Tender F (castF W) k): Tender F (castF (occult W)) k:=by
  let d:= newbornL n; let B:=castF W; let G := F-B
  let e:ℝ:= (2:ℝ)⁻¹
  have hv : castF (occult W)=e • (B+d∘B):=rfl
  have ht : F-castF (occult W)=ᶠ[𝓝 0] e • (G+d∘G):=by
    filter_upwards [h.chiral] with x hx; rw [hv]; change F x-e • (B x+d (B x))=e • ((F x-B x)+ d (F x-B x)); rw [map_sub, show d (F x)=F x from hx.symm]
    rw [show (F x-B x)+(F x-d (B x))=(F x+F x)-(B x+d (B x)) by abel,smul_sub,← two_smul ℝ _, smul_smul, show e*2=1 by unfold e; norm_num,one_smul]
  have hb:ContDiffAt ℝ ω B 0:=he.2.2
  have hp : ContDiffAt ℝ ω G 0:=he.2.1.sub hb; have hk : ContDiffAt ℝ ω (d∘G) 0:= d.contDiff.contDiffAt.comp _ hp
  refine ⟨fun i hi=>?_,he.2.1,hv ▸ ContDiffAt.const_smul e (show ContDiffAt ℝ ω (B+ d ∘ B) 0 from hb.add (d.contDiff.contDiffAt.comp (f:=B) _ hb))⟩
  rw [(ht.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_const_smul_apply (f:=(G+d∘G)) ((hp.add hk).of_le le_top), iteratedFDeriv_add_apply (hp.of_le le_top) (hk.of_le le_top), d.iteratedFDeriv_comp_left hp le_top,show iteratedFDeriv ℝ i G 0=0 from he.1 i hi]; ext; simp

lemma Eternal (k:ℕ)(hk:k≤2)(ht:0<u)(hb:0≤b) : ∃ a W,0<a∧0 ≤ W ∧∀ (S:SparkMesh) (F:S.Field), Clan S F→ (∀ i, Eyrie.glyph (traceG _) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (F i) u b)→(∀ n,EmptyThrough (F n) k)→
    (∀ i, Noble (F i)) → ∃ P:Fruited (Snug k)→Bloom k, Fractal P a W ∧ (∀ n,Majestic (dust P n)) ∧ ∀ i,Tender (F i) (castF (dust P _)) (k+1):=by
  obtain ⟨v,C,h,hc,H⟩:= Sparks.issue k hk ht hb
  let a:=v/(1+k:ℝ); have ha:0<a:=by unfold a; positivity
  refine ⟨a,ceiling v k C,ha,mul_nonneg (Real.exp_pos _).le hc,fun S F hi he ht hk=>?_⟩
  obtain ⟨P,haP,H⟩:=H _ _ hi he ht
  refine ⟨frosting P,coined a ha.le haP (le_of_eq (div_mul_cancel₀ _ (by positivity))),fun _=>coined_port haP,fun i=>?_⟩
  rw [coined_inv haP]; exact donate (hk i) (agree_test (hk i) ⟨H i,hi.way i|>.ready,serenity haP h⟩)
lemma Noble.less {G: trackG n}(h:Noble F)(he:Noble G): Noble (F-G):=by
  refine ⟨fun t=>?_,?_⟩
  · filter_upwards [h.praised t,he.praised t] with x hx hv; simp only [Pi.sub_apply, aura_sub,hx,hv]
  filter_upwards [h.chiral,he.chiral] with x hx hv; change _=newbornL n (F x-G x); rw [map_sub]; exact congr_arg₂ (·-·) hx hv
lemma Majestic.told {A:LegInk n}(h: Majestic A): Noble (castF A):= Noble.religious h.port h.lane
end YM.QCD.Revolve
