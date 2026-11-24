import YM.MassiveQCD.Evolution.Gather
/-! # Forced analytic path retreat
 Produce NEW K at all powers; full-budget and sym at real marker given certain repeat estimates.
 Caller uses `portendsR`, adapted for many tag activations BEFORE K projection.
 `sum` is pointwise identity retaining exact α encoding; use companion exactly from sort.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open MassiveQCD.Analysis.Shelf Metric
variable {c:Side}{N n B:ℕ}{t s r δ T τ u :ℝ}{i:Site c} {ι : Type}
local notation "Ω"=> EvenA c N
variable (p:Patron.Rail c N ι)
-- Quits + Countable. no positive density proof in tilt.
variable [Countable ι]
omit [Countable ι] in
lemma income (U:Grid c)(ht:1≤t)(hh:1≤τ)(hc:Quits p B u τ δ t)(hδ:0≤δ): Summable fun i=> ‖p.warp i U‖:=by
    obtain ⟨f,hf,h⟩:=hc.cost; have hx i:0≤f i :=(norm_nonneg _).trans (h i 1); let g:= GasP.taxed (oriD p) f τ; have he i: f i ≤ g i:=le_mul_of_one_le_left (hx _) (one_le_pow₀ hh)
    have hF: Summable g:= Loom.fishes _ _ hf (fun i=>(hx i).trans (he _)) hδ (fun i _=> (p.addr i).alive.mono (p.addr i).part); exact hF.of_nonneg_of_le (fun i=> norm_nonneg _) (fun i=> (Loom.tore _ ht).trans ((h _ U).trans (he _)))
omit [Countable ι] in
lemma profits (U:Grid c)(ht:1 ≤ t)(hh:1≤τ)(hc:Quits p B u τ δ t)(hδ:0≤δ) (r:ℝ) : Summable (tK p r U):=by
    let f i:= p.warp i U; have he: Summable (fun i:Finset ι=> ∏ j∈i, ‖f j‖):= summable_finsetProd_of_summable_nonneg (fun i=> norm_nonneg _) (income p U ht hh hc hδ); refine Summable.of_norm_bounded he (fun i=>?_); unfold tK; split; exact norm_prod_le ..; rw [norm_zero]; exact prod_nonneg fun _ _=> norm_nonneg _
namespace LanternK
variable (Y:LanternK c N ι)
variable (Hq:Y.ChargedK u r t T B δ τ)(v:ℝ)
include Hq
omit [Countable ι] in
lemma publish (hv:0 ≤ v)(hx:v≤1/4)(ht:1≤t)(hh:1≤τ)(hδ:0≤δ)(z:ℂ)(hz:‖z‖≤1) (U:Grid c) : heartK (lampK (Y.phased v) Prod.snd z) r U= heartK (Y.get (z*v)) r U:=by
    let K:=lampK (Y.phased v) Prod.snd z; have hS:Summable (tK K r U):= profits _ _ ht hh (lampB (Y.phased v) z (breaks Y Hq v hv hx) hz Prod.snd) hδ _ -- argument order
    let P:= Y.get (z*v); have hp: ∀ i, HasSum (fun n=>K.warp (i,n) U) (P.warp i U):=fun i=> speakeasy Y Hq v z i U hv (lt_of_le_of_lt hx (by norm_num)) hz
    unfold heartK; symm; apply HasSum.tsum_eq; apply (hS.hasSum.tsum_fiberwise Gather.stage).congr_fun
    intro i; exact (Gather.wind P K rfl i r U hp hS).tsum_eq.symm
-- base all-f flavors at zero. test all ranks at true K, t budget. public zero toggles
omit [Countable ι] Hq in
lemma unmarked (hr: MixedP (Y.get 0)) : MixedP (lampK (Y.phased v) Prod.snd 0):=by
   let X:= lampK (Y.phased v) Prod.snd 0; let G:= Y.get 0; have h (i:ι)(j:ℕ)(U:Grid c): X.warp (i,j) U= if j=0 then G.warp i U else 0:=by
      change (0:ℂ)^j • ((v:ℂ)^j • ampK (fun u=>Y.actsK u i U) j) = _; by_cases he:j=0; · subst j; rw [pow_zero,pow_zero,one_smul,one_smul,amp_zero]; simp; rfl
      simp [he]
   have he (f:Ω→+*Ω) (i j:ι) (k:ℕ)(U V:Grid c)(hv:f (G.warp i U)=G.warp j V): f (X.warp (i,k) U)=X.warp (j,k) V:=by simp_rw [h]; split; exact hv; exact map_zero _
   refine ⟨?_,?_,?_,fun s z k hk=>?_⟩
   · rintro ⟨i,n⟩ U k; exact congr_arg Subtype.val (he (sways (Lat.rotates N k)) i i n (Lattice.gauge k U) U (Subtype.ext (hr.gauge i U k)))
   · rintro ⟨i,n⟩ U X hX; exact he _ _ _ n U _ (hr.num i U X hX)
   · rintro ⟨i,n⟩ U; exact he _ _ _ n U _ (hr.real i U)
   obtain ⟨p,hp⟩:=hr.moves s z k hk; refine ⟨Equiv.prodCongr p (Equiv.refl _),?_⟩; rintro ⟨i,n⟩; exact ⟨(hp i).1,(hp i).2.1,fun U=>he _ i _ n _ _ ((hp i).2.2 U)⟩
end LanternK
end YM.QCD.Ruby
