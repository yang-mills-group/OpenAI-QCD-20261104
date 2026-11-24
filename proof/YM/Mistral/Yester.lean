import YM.Mistral.Hut
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
variable (r:Patrol P)
set_option quotPrecheck false
local notation "n'"=> r.size
local notation "It"=> Fin (r.size)
local notation "T"=>C.S
local notation "a" i:arg=> C.S.spacing (C.N i)
local notation "V"=>Fin.cons (0:E4) r.land
local notation "Λ"=>Fin.cons (0:Cover)
local notation "s1" i:arg=> pollF C (r.size+1) i (Fin.cons 0 (r.way i))
local notation "f" i:arg k:arg=> r.hall i k (r.way i k)
noncomputable def Patrol.material (i:ℕ):= (List.ofFn fun k=>r.hall i k (r.way i k)).prod
noncomputable abbrev Patrol.glory (W:Choir) (s:W.W):= W.total (n'+1) (points (Fin.cons 0 r.land)) (Fin.cons s (fun i=> W.focus none _ (r.texts i)))
noncomputable def Patrol.gleam (W: Choir)(x:E4)(v p:W.W):= W.total (n'+2) (points (Fin.cons x (Fin.cons 0 r.land))) (Fin.cons v (Fin.cons p (fun i=>W.focus none _ (r.texts i))))
variable (H:∀ d,Cottage P d){φ:ℕ→ℕ}(hpφ:Tendsto φ atTop atTop)(hW:W.Harmony P φ)(hz:Sway C.S)
variable (u v:ℕ→Label d)(x y:Label d)(hu:Tracked P d u φ x)(hv:Tracked P d v φ y)
variable (K:E4)(q:ℕ→ Cover)(hK:Tendsto (fun i=>digit (C.S.spacing (C.N i)) (q i)) atTop (𝓝 K))(hQ:points (Fin.cons K (Fin.cons 0 r.land))∈conf (r.size+2))
include hp hW hpφ hz H
local notation "p!" i:arg=> (C.A i).regulator
local notation "vi" i:arg=> φ i
local notation "v₀" i:arg=> stem P d i (u i)
local notation "vP" i:arg=> stem P d i (v i)
local notation "X"=> W.focus none d x
local notation "Y"=> W.focus none d y
open _root_.YM.Fir.NoteF
-- mixture authenticated limit.Font Bonded.
include hu
lemma Patrol.tarifs : Tendsto (fun i=> ((p! (φ i)).average (((v₀ (φ i)) 0)* (r.material (φ i))))) atTop (𝓝 (Patrol.glory r W (W.focus none d x))):=by
        let F:Fin (r.size+1)→ℕ:= Fin.cons d r.stars; let X' : (i:Fin (r.size+1))→ℕ→Label (F i):=Fin.cons (α:=fun i=>ℕ→Label (F i)) u (fun i _=>r.texts i); let p:(i:Fin (r.size+1))→ Label (F i):= Fin.cons (α:=fun i=>Label (F i)) x r.texts
        have h(k:Fin (r.size+1)):Tracked P (F k) (X' k) φ (p k):=Fin.cases (show Tracked P (F 0) (X' 0) φ (p 0) from hu) (fun i =>by apply tracksZ; exact tendsto_const_nhds; exact ⟨‖p i.succ‖,norm_nonneg _,Eventually.of_forall (fun _=>by exact le_rfl)⟩) k -- need motives.Res.
        let q:= points (Fin.cons (0:E4) r.land); have hm:= supra W hpφ hW hp hz H F X' p q r.ok h
        let F0(i:ℕ):Fin (r.size+1)→ Cover:= Fin.cons (0:Cover) (r.way (φ i)); have he:Tendsto (fun i:ℕ=> (i,F0 i)) atTop (Watch C φ q):= NoteF.ride _ _ tendsto_id ((r.travel hp).comp hpφ) -- motive infer
        have ht:=hm.comp he; have hY(k:Fin (r.size+1)): W.focus none (F k) (p k)=Fin.cons (α:=fun _=>W.W) X (fun i=> W.focus none _ (r.texts i)) k:=by induction k using Fin.cases <;> rfl
        change Tendsto _ _ (𝓝 (W.total (n'+1) q (Fin.cons X _))); rw[← funext hY]; refine ht.congr fun i=>?_; change readS .. = _; unfold readS; rw[List.ofFn_succ,List.prod_cons]; rfl
include hv hK hQ
lemma Patrol.treat : Tendsto (fun i=> ((p! (φ i)).average (((v₀ (φ i)) (q (φ i))) * ((vP (φ i)) 0) * r.material (φ i)))) atTop (𝓝 (Patrol.gleam r W K (W.focus none d x) (W.focus none d y))):=by
        let D₀:Fin (r.size+1)→ℕ:= Fin.cons d r.stars; let F:Fin (r.size+2)→ℕ:=Fin.cons d D₀
        let X': (i:Fin (r.size+2))→ ℕ→ Label (F i):= Fin.cons (α:=fun i=>ℕ→ Label (F i)) u (Fin.cons (α:=fun i=>ℕ→ Label (D₀ i)) v (fun i _=>r.texts i)); let p:(i:Fin (r.size+2))→Label (F i):= Fin.cons (α:=fun i=>Label (F i)) x (Fin.cons (α:=fun i=> Label (D₀ i)) y r.texts)
        have h(k:Fin (r.size+2)):Tracked P (F k) (X' k) φ (p k):=by
             induction k using Fin.cases with
             | zero=>exact hu
             | succ k=> induction k using Fin.cases with
                        | zero=> exact hv
                        | succ k => apply tracksZ; exact tendsto_const_nhds; exact ⟨‖p k.succ.succ‖,norm_nonneg _,Eventually.of_forall fun i=> (show _ from le_refl _) ⟩
        let Xp:= points (Fin.cons K (Fin.cons 0 r.land)); have ht:= supra W hpφ hW hp hz H F X' p Xp hQ h
        have hv:Tendsto (fun i:ℕ=> (i,r.Y q (φ i))) atTop (Watch C φ Xp):= NoteF.ride _ _ tendsto_id ((r.breeze hp K q hK).comp hpφ)
        have hh : (fun k=> W.focus none (F k) (p k))=Fin.cons X (Fin.cons (W.focus none d y) (fun i=> W.focus none _ (r.texts i))):=by
             funext k; induction k using Fin.cases with
             | zero=>rfl
             | succ k=> induction k using Fin.cases <;> rfl
        unfold Patrol.gleam; rw [←hh]; refine (ht.comp hv).congr fun i=>?_; rw [mul_assoc]; change readS ..=_ ; unfold readS; rw[List.ofFn_succ,List.ofFn_succ,List.prod_cons,List.prod_cons]; rfl
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Patrol.treat
#print axioms YM.Massive.Tarn.Choir.Patrol.tarifs
