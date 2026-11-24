import YM.Gust.Slick
import YM.Gust.Blank
set_option autoImplicit false
set_option maxHeartbeats 860000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix Classical
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n:ℕ}{x:Points m}(hx:x∈conf m)
variable (v:Fin m→ Stake T n)(u:Fin m→Mater T n)(a:Axis)(s:Equiv.Perm (Fin m))
local notation "Z"=> Fin m → Stake T n
-- Permute helper
lemma turn_up {α β:Type*} (a:Fin m→α)(i:Fin m)(x:α)(s:Equiv.Perm (Fin m)) (b:α→β) : b ∘(update a i x ∘s)= update (b∘(a ∘s)) (s.symm i) (b x):=by
    funext j; by_cases h:j=s.symm i; · subst j; simp
    have h':s j≠i:=by intro h'; exact h (s.injective (by simpa using h'))
    simp [h,h']
include hf hx
lemma aired : ValueP (Points.rearrange s x) (u ∘ s)= ValueP x u:=by
     simp_rw [← fit]; symm; refine kiosks hf _ _ ?_ ?_
     · exact (s.ofFn_comp_perm (fun i=>(x i,u i))).symm
     simp only [Piers,stageP,List.map_ofFn,List.nodup_ofFn]; exact hx
lemma movedB: valuation T n m (Points.rearrange s x) (v ∘ s)=valuation T n m x v :=by
      let f(r:Z):= valuation T n m (Points.rearrange s x) (r ∘ s); let g:= valuation T n m x; change f v=g v; refine recurs (fun i=>f i=g i) ?_ ?_ ?_ ?_ v
      · intro a i h; exact Eq.trans ((valuation ..).map_coord_zero (s.symm i) (by simp[h])) (g.map_coord_zero i h).symm
      · intro a; exact (values (Points.rearrange s x) (a ∘ s)).trans ((aired hf hx a s).trans (values x a).symm)
      · intro a i x y h k
        unfold f at *; simp_rw [show ∀ r:Stake T n, update a i r ∘s= update (a ∘ s) (s.symm i) r from fun r=>turn_up a i r s id] at *; rw [MultilinearMap.map_update_add,h,k,g.map_update_add]
      · intro a i x h c; unfold f at *; simp_rw[show ∀ r: Stake T n, update a i r∘s=update (a ∘ s) (s.symm i) r from fun r=>turn_up a i r s id] at *; rw [MultilinearMap.map_update_smul,h,g.map_update_smul]
variable {σ:Signed}{p:EuPin}(hp:p.Lifts σ) (Y:E4)
lemma acrossP: valuation T n m (Points.across Y x) v= valuation T n m x v :=by
      let G:=valuation T n m (Points.across Y x); let H:=valuation T n m x; refine recurs (fun v=>G v=H v) (fun a i h=>Eq.trans (G.map_coord_zero i h) (H.map_coord_zero i h).symm) (fun a=>?_) (fun a i x y h k=>by rw[G.map_update_add,H.map_update_add,h,k]) (fun a i x h c=>by rw[G.map_update_smul,H.map_update_smul,h]) _
      unfold G H; rw [values,values]; unfold ValueP; simp_rw [hf.translation m x hx]
open Finset
lemma peaks:ValueP (Points.move p.coord x) (fun i=> act hK hp (u i))= ValueP x u:=by
     unfold ValueP; apply congr_arg₂ (·*·); rfl; exact prod_congr rfl fun i _=> hf.discrete m x hx p σ hp _
lemma climbs: valuation T n m (Points.move p.coord x) (axisK hK hp T n∘ v) = valuation T n m x v :=by
      let f:= axisK hK hp T n; let A:= valuation T n m (Points.move p.coord x); let F:= A.compLinearMap (fun i:Fin m=>f); let g:=valuation T n m x; refine recurs (fun v=>F v=g v) (fun a i h=> Eq.trans (F.map_coord_zero i h) (g.map_coord_zero i h).symm) (fun a=>?_) (fun a i x y h k=>by rw[F.map_update_add,g.map_update_add,h,k]) (fun a i x h c=>by rw[F.map_update_smul,g.map_update_smul,h]) _
      unfold F A g f; rw [MultilinearMap.compLinearMap_apply]; simp_rw [pin_pl]; rw [values,values]; exact peaks hK hf hx a hp
noncomputable abbrev Xψ(p:Points m)(a:Axis):= Points.move (Signed.reflect a) p
lemma reflectsG : ValueP (Xψ x a) (fun i=> tint hK a (u i))=star (ValueP x u):=by
      let g:=stageP u x; let B:= stageP (fun i=> tint hK a (u i)) (Xψ x a); have hg: Piers g:=by simp only[Piers,g,stageP,List.map_ofFn,List.nodup_ofFn]; exact hx
      have hv: backward hK g a=B.reverse:=by unfold B g backward stageP; rw [List.map_reverse,List.map_ofFn]; rfl
      simp_rw[←fit]; change gate B=star (gate g); rw[←washed hK hf _ _ hg, hv] -- infer a
      refine kiosks hf _ _ (List.reverse_perm _).symm ?_; simp only [Piers,B,stageP,List.map_ofFn,List.nodup_ofFn]; exact Points.move_in _ hx
lemma conj_poses:valuation T n m x (barK hK a T n ∘ v)=star (valuation T n m x v):=by
       let A:=valuation T n m x; let f:=barK hK a T n; refine recurs (fun v=>A (f ∘ v)= star (A v)) ?_ (fun u=>?_) ?_ ?_ _
       · intro u i h; rw [A.map_coord_zero i h,A.map_coord_zero (m:=f ∘u) i (by simp[h]),star_zero]
       · let Qz:=(f ∘ fun i=>plant (u i)); have hh: valuation T n m (Xψ x a) (fun i=>plant (tint hK a (u i)))=star (A (fun i=> plant (u i))):= (values (Xψ x a) _).trans ((reflectsG hK hf hx u a).trans (congr_arg star (values x u).symm))
         have h:=climbs hK hf hx Qz (couture a); have hV:axisK hK (couture a) T n ∘ Qz= (fun i=> plant (tint hK a (u i))):=by unfold Qz f; simp_rw [comp_def,bar_pl,pin_pl,didD]
         rw[hV,show (flipC a).coord= Signed.reflect a from couture _] at h; exact h.symm.trans hh
       · intro p i x y h k; have hh(r:Stake T n): f∘update p i r= update (f ∘ p) i (f r):= by funext j; by_cases hb:j=i <;> simp [hb]
         rw [hh,map_add,A.map_update_add,A.map_update_add,←hh,←hh,h,k,star_add]
       · intro p i x h c; have hh(r:Stake T n): f∘update p i r= update (f ∘ p) i (f r):= by funext j; by_cases hb:j=i <;>simp [hb]
         rw[hh,map_smulₛₗ,A.map_update_smul,A.map_update_smul,←hh,h,star_smul]; rfl
end YM.Massive.Gust
#print axioms YM.Massive.Gust.movedB
#print axioms YM.Massive.Gust.conj_poses
