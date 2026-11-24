import YM.Mistral.Site
import YM.Mistral.Daze
/- Ar.o estimator.V.Work, extension contacts. Tests finite labels arbitrary.  -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function Set Metric Filter QCD Lat Lattice UV Patria Patria.Depth
open Poised Plans Plans.Stamp Intag Intag.Vale Finset
open scoped Topology BigOperators Matrix ComplexOrder ContDiff Classical
variable {d:ℕ}
open Needle Needle.GaugeP Hub YM.Fir YM.Massive.Fir
variable {C:Sequence}{P:Calibration C} {n m:ℕ}
variable {x e:ℝ}(hp:C.Path x e) (W: Choir)

-- labels ext arbitrary.Count.Test all.Progress. Pin.a.Slope level j,H.
structure Patrol (P:Calibration C) where
    (size:ℕ)
    (stars:Fin size→ℕ)
    (texts:(i:Fin size)→Label (stars i))
    (land:Fin size→ E4)
    ok: points (Fin.cons 0 land)∈ conf (size+1)
-- observer-independent ports.Per.Le.A.
variable (r:Patrol P)
set_option quotPrecheck false
local notation "n'"=> r.size
local notation "It"=> Fin (r.size)
local notation "T"=>C.S
local notation "a" i:arg=> C.S.spacing (C.N i)
noncomputable def Patrol.way (i:ℕ)(t:Fin r.size): Cover:= bead (C.S.spacing (C.N i)) (r.land t)
noncomputable abbrev Patrol.hall (i:ℕ)(t:Fin r.size) : Needle.stalk C i:= stem P (r.stars t) i (r.texts t)
noncomputable def Patrol.Y (f:ℕ→ Cover)(i:ℕ):Fin (r.size+2)→ Cover:=Fin.cons (f i) (Fin.cons 0 (r.way i))
local notation "V"=>Fin.cons (0:E4) r.land
local notation "Λ"=>Fin.cons (0:Cover)
local notation "s1" i:arg=> pollF C (r.size+1) i (Fin.cons 0 (r.way i))
include hp
namespace Patrol
lemma travel:Tendsto (fun i=>s1 i) atTop (𝓝 (points (Fin.cons 0 r.land))):=by
        let f:= fun i=> s1 i; let Z:= PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (r.size+1)=> E4); let P:=points (Fin.cons 0 r.land)
        have hp' : Tendsto (Z ∘ f) atTop (𝓝 (Z P)):=by
              apply tendsto_pi_nhds.mpr; intro i; induction i using Fin.cases with
              | zero=> exact (show Tendsto (fun _ :ℕ=> (0:E4)) atTop (𝓝 0) from tendsto_const_nhds).congr (fun j=> (Needle.digit_zero _).symm) -- order
              | succ i=> exact approaches hp _
        have h:=(Z.symm.continuous.tendsto (Z P)).comp hp'; rw [Z.symm_apply_apply] at h; exact h.congr fun i=>Z.symm_apply_apply _
variable (u:E4)(F:ℕ→ Cover)
lemma breeze(hx:Tendsto (fun i=> digit (a i) (F i)) atTop (𝓝 u)): Tendsto (fun i => pollF C _ i (r.Y F i)) atTop (𝓝 (points (Fin.cons u (Fin.cons 0 r.land)))):=by
         let q:=points (Fin.cons u (Fin.cons 0 r.land)); let Z:= PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (r.size+2)=> E4); let f(i):= pollF C _ i (r.Y F i)
         have hh(i:Fin (r.size+2)): Tendsto (fun k=> Z (f k) i) atTop (𝓝 (Z q i)):=by
               induction i using Fin.cases with
               | zero=> exact hx
               | succ i=>
                 induction i using Fin.cases with
                 | zero=>exact (show Tendsto (fun _ :ℕ=> (0:E4)) atTop (𝓝 0) from tendsto_const_nhds).congr (fun j=>(Needle.digit_zero _).symm)
                 | succ i=>exact approaches hp _
         have h:=(Z.symm.continuous.tendsto (Z q)).comp (show Tendsto (⇑Z ∘f) atTop (𝓝 (Z q)) from (tendsto_pi_nhds.mpr hh)); rw [Z.symm_apply_apply] at h; exact h.congr fun i=>Z.symm_apply_apply _
abbrev Luminous (j:ℕ)(q:Fin r.size→ℝ) : Prop := (∀ i, 0≤q i) ∧ 40*(r.size+1) ≤ (C.S.step j).L.val ∧ ∀ᶠ i in atTop,(∀ t: Fin r.size, GreenP C i j (r.hall i t) (q t)) ∧ seaM C i j (Fin.cons (0:Cover) (r.way i))
variable (K:∀ d,Cottage P d)(hS:Sway C.S)
include K hS
lemma funding : ∀ᶠ j in atTop,∃ q,r.Luminous j q:=by
      have hT :∀ᶠ j:ℕ in atTop,∀ i:Fin r.size,∃ v:ℝ,0≤ v∧∀ᶠ k in atTop, GreenP C k j (r.hall k i) v:=by
           refine eventually_all.mpr (fun i=>?_); exact ((K _).pointsP hp hS none (fun _=>r.texts i) ⟨_,norm_nonneg _, Eventually.of_forall (fun _=>le_rfl)⟩).1
      obtain ⟨u,hu,h⟩:=Fir.seascape (φ:=id) hp tendsto_id r.ok; have hx: Tendsto (C.S.spacing) atTop (𝓝 0):=by -- directly S not A.C.N; spacing antitone
           refine Metric.tendsto_nhds.mpr fun x hx=>?_
           obtain ⟨p,h⟩:=((tendsto_nhds_of_tendsto_nhdsWithin hp.physical).eventually_lt_const hx).exists
           filter_upwards [eventually_ge_atTop (C.N p)] with i hi; rw[dist_zero_right,Real.norm_of_nonneg (space0 _ _|>.le)]; exact lt_of_le_of_lt (spacing_antitone _ hi) h
      have hl:Tendsto (fun i:ℕ=>(i,Fin.cons (0:Cover) (r.way i))) atTop (Watch C id (points (Fin.cons (0:E4) r.land))):= NoteF.ride _ _ tendsto_id (r.travel hp) -- verify signature
      filter_upwards [hx.eventually_lt_const hu,hS.high.eventually_ge_atTop (40*(r.size+1)),hT] with j hu hG ht; choose v hv H using ht; refine ⟨v,hv,hG,?_⟩
      filter_upwards [eventually_all.mpr H,hl.eventually h,hp.uv.tendsto_atTop.eventually_ge_atTop j] with i h hP hX; exact ⟨h,tide _ _ _ hP hX hu⟩
end Patrol
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Patrol.funding
