import YM.Lobo.Mallet
import YM.Lobo.Oar
import YM.Lobo.Nodal
set_option autoImplicit false
set_option maxHeartbeats 620000
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole UV.Free Iceberg
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Finset
open scoped YM.Massive.Poised.Plans.Stamp
variable (k i j: Tri) (b:IceT) -- replace
variable {d:ℕ}(v:Label d)(w:Tri→Label d)(Z:Tri→Tri→Label d)
local notation "CA"=> Cane (pathW k) (Omega k) (treks k)
noncomputable abbrev rho (b u:IceT)(t:ℝ):ℝ := if b=u then t else 0
lemma coreT (b u:IceT)(t:ℝ):let Q:=sectorP b (pathW k t); (u.elim Q.1 Q.2).coord= Thr k (rho b u t) :=by
    intro Q; by_cases h:b=u; · subst u; rw [rho,if_pos rfl]; refine Eq.trans ?_ ((treks k).2.2 t); apply congr_arg EuPin.coord; unfold Q sectorP; cases b <;> simp [aPaneB, bPaneB,maskH]
    rw [rho,if_neg h,Thr,carry_one]; have ht:u.elim Q.1 Q.2=(1:EuPin):=by unfold Q sectorP; cases b <;> cases u<;> simp [aPaneB,bPaneB,maskH] at * <;> simp [*,aPaneB,bPaneB,maskH]
    rw [ht]; rfl
lemma freeK(K:EuPin)(s:RawSym) (p:Label d) : s.pin d K p=putH (K,plainPicture K) d p:= Subtype.ext ((s.pinActs _ _ _).trans (spine_pin ..).symm)
lemma oneP(K:EuPin): b.elim K (plainPicture K)=K:=by cases b<;>rfl
lemma cusP(K:EuPin)(h:K.Lifts (Cup k)): (b.elim K (plainPicture K)).coord=Thr k quarterR:=by rw[oneP]; exact h.trans (Maxwell.Free.Corners.sendsTime _ _ (fun h=>threeL k (Fin.castSucc_inj.mp h))) -- h type abbrev
set_option quotPrecheck false
lemma grit (u:IceT)(hx:Lone b v): Cane (pathW k) (Omega k) (treks k) u d v=0:=by
    have he:= tCane (pathW k) _ (treks k) u v; have h(t:ℝ):putH (sectorP u (pathW k t)) d v=v:=hx.cov _ _ _ _ (coreT k u b t); simp_rw[h] at he; exact he.unique (hasDerivAt_const ..)
lemma gain (u:IceT)(hx:Brook b w): Cane (pathW k) (Omega k) (treks k) u d (w i) = if u=b then drive k w i else 0:=by
    have he:= tCane (pathW k) _ (treks k) u (w i); have h(t:ℝ):putH (sectorP u (pathW k t)) d (w i)=wing k (rho u b t) w i:=hx.cov _ _ _ _ (coreT k u b t) _; simp_rw[h] at he
    split_ifs with H; · subst u; simp only [rho,  ↓reduceIte] at he; exact he.unique (wingD k i w)
    simp only [rho,H,↓reduceIte,w_zero] at he; exact he.unique (hasDerivAt_const ..)
lemma gainer (u:IceT)(hX:BraceP b Z): Cane (pathW k) (Omega k) (treks k) u d (Z i j)=if u=b then drive k (fun i=> Z i j) i+drive k (Z i) j else 0 :=by
    have he:= tCane (pathW k) _ (treks k) u (Z i j); have h(t:ℝ):putH (sectorP u (pathW k t)) d (Z i j)=wing k (rho u b t) (fun i=> wing k (rho u b t) (Z i) j) i:=hX.cov _ _ _ _ (coreT k u b t) i j; simp_rw [h] at he
    split_ifs with H; · subst u; simp only [rho, ↓reduceIte] at he; exact he.unique (swellP k i (fun a t=> wing k t (Z a) j) (fun i=> Z i j) (fun i=>drive k (Z i) j) (fun v=>w_zero k j (Z v)) (fun a=> wingD k j (Z a))) -- ? V.
    simp only[rho,H,↓reduceIte,w_zero] at he; exact he.unique (hasDerivAt_const ..)
noncomputable abbrev omegaQ(k:Tri)(u:IceT→ℝ)(d:ℕ): Module.End ℂ (Free.Symbol d):= reachΩ (Omega k) (pathW k) (treks k) u d
variable (p:RawSym)(s:Hail.RightAuth p)(u:IceT→ℝ)
include s
lemma atL(hx:Lone b v): omegaQ k u d (Free.projection v)=0:=by unfold omegaQ reachΩ; simp_rw[LinearMap.sum_apply,LinearMap.smul_apply,fun c:IceT=> joins (pathW k) (Omega k) (treks k) c p s v,fun c:IceT=>grit k b v c hx,map_zero,smul_zero,sum_const_zero]
lemma atB (hx:Brook b w): omegaQ k u d (projection (w i))= (u b:ℂ) • drive k (projection ∘ w) i:=by
     unfold omegaQ reachΩ; simp_rw[LinearMap.sum_apply,LinearMap.smul_apply,fun c:IceT=> joins (pathW k) (Omega k) (treks k) c p s (w i), fun c=> gain k i b w c hx]; rw [sum_eq_single b]; · rw [if_pos rfl]; unfold drive; simp only[_root_.map_sum,map_smul]; rfl
     · intro z _ h; rw [if_neg h,map_zero,smul_zero]
     simp
lemma atS (hx:BraceP b Z): omegaQ k u d (projection (Z i j))= (u b:ℂ) • (drive k (fun a=>projection (Z a j)) i+ drive k (projection ∘Z i) j):=by
     unfold omegaQ reachΩ; simp_rw[LinearMap.sum_apply,LinearMap.smul_apply,fun c:IceT=> joins (pathW k) (Omega k) (treks k) c p s (Z i j), fun c=> gainer k i j b Z c hx]; rw [sum_eq_single b]; · rw[if_pos rfl,map_add]; unfold drive; simp only[_root_.map_sum,map_smul]; rfl
     · intro z _ h; rw[if_neg h,map_zero,smul_zero]
     simp
omit s
lemma asL (hx:Lone b v): p.pin _ (SpinQ k) v=v:=by rw [freeK]; exact hx.cov _ _ _ _ (cusP k b _ (fL _))
lemma asB(hx:Brook b w): p.pin _ (SpinQ k) (w i)= (charI k i:ℂ) • w (roof k i):=by rw [freeK,hx.cov _ _ _ _ (cusP k b _ (fL _)),wing_Q]
lemma asS(hx:BraceP b Z): p.pin _ (SpinQ k) (Z i j)= (charI k i:ℂ) • ((charI k j:ℂ) • Z (roof k i) (roof k j)):=by rw[freeK,hx.cov _ _ _ _ (cusP k b _ (fL _)),wing_Q]; simp_rw [wing_Q]
end YM.Lobo
#print axioms YM.Lobo.atS
#print axioms YM.Lobo.atB
#print axioms YM.Lobo.asB
#print axioms YM.Lobo.asL
#print axioms YM.Lobo.atL
#print axioms YM.Lobo.asS
