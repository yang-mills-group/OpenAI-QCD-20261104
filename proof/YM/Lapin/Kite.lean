import YM.Lapin.Cycle
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast.Rays
variable {D:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
variable (a b:Flavor 6) (s t:Axis)(g:su.Color)(e:ℤ)(u:Averaging)(j j':Fiber)
local notation "φ"=> A.density i
variable (F:Cover→Insertion (S.side R m) 6)(ht:i ≤ m)
local notation "F★" V:arg=>foil φ (Gall.viaP A V u i)
local notation "α" V:arg=> report A V u i
local notation "β" V:arg=> foil φ ((α V) 0)
local notation "r"=> helm M
local notation "o2"=> oracle2
local notation "μ"=> (Fintype.card (Site M):ℂ)
variable (hk:1 ≤ k) (hv:∀ᶠ V:Grid (S.side R i) in 𝓝 1, IsUnit (A.density i V))
include hk
omit hk in
private lemma sunset {I:Type} (G:I→Density c 6)(q:Finset I)(h:∀ i∈q,Chart k (G i) 1):Chart k (∑ i∈q,G i) 1:=by unfold Chart; simp_rw[Function.comp_def,Finset.sum_apply]; apply ContDiffAt.sum; exact h
private lemma sunset' {I:Type} (G:I→Density c 6)(q:Finset I)(h:∀ i∈q,Chart k (G i) 1):rub g (∑ i∈q,G i) (waveZ e s t)= ∑ i∈q,rub g (G i) (waveZ e s t):=by
       induction q using Finset.induction_on with
       | empty=> simp [rub,tent,Function.comp_def]
       | insert i q hh ih=>
          have hu:∀ i∈q, Chart k (G i) 1:=fun i hi=> h i (mem_insert_of_mem hi)
          rw[sum_insert hh,rub_plus (G i) _ g _ (h i (by simp)) hk (sunset _ q hu),ih hu,sum_insert hh]
include hA hi ht hv
lemma praise (hD:TideT A u m (report A F u))(hF:Chart k (β F) 1) : Chart k (F★ F) 1 ∧ o2 e s t a j j' g (F★ F)= μ * o2 e s t a j j' g (β F):=by
       let Z(b):= foil φ ((α F) b); let J:= Z 0; have he(x:Cover):(φ)=march x φ:=by rw [pier A hA hi]; exact (Patria.Depth.first A i hi x).symm
       have hh(x): march x ((α F) 0)=⇑((α F) x):=(by simpa only [zero_add] using ((hD.moves i ht).trans x 0)); have hY(x): Z x=ᶠ[𝓝 1] march x (Z 0):=by unfold Z; rw [← hh]; exact course x _ _ hv (he _).symm
       have hK(x:Cover): Chart k (Z x) 1:= frugal _ _ (hY x) (marchC x (Z 0) hF); have hz : foil φ (Gall.viaP A F u i)= ∑ i':Site M,Z (Lattice.lift i'):=by funext x; unfold viaP foil; rw [ContinuousMap.sum_apply,mul_sum,Finset.sum_apply]
       rw [hz]; constructor; · exact sunset _ _ fun i _=> hK _
       have hw(x): o2 e s t a j j' g (Z x)= o2 e s t a j j' g J:=by
            rw [←divine2 J x g e s t a j j' hF hk]; unfold oracle2; rw [rub_eq _ _ g (hY x)]
       rw [oracle2,sunset' s t g e hk _ _ (fun i _=> hK _),map_sum]; change (∑ i:Site M,oracle2 e s t a j j' g (Z (lift i)))=_; simp_rw [hw,sum_const,card_univ,nsmul_eq_mul]; rfl
local notation "G"=> marque (i:=i) A true a s
local notation "Γ"=>ms (i:=i) a A
local notation "kΔ"=> slope M 1 s s-slope M 0 s s
omit ht
lemma weight1 (hF: Chart k (foil φ (report A G u i 0)) 1)(hY:Chart k (foil φ (report A Γ u i 0)) 1)(ht:s≠t) :river2 s t b j j' g (β G)= if b=a then ((r)⁻¹*(kΔ)) * (∑ z:Fiber,wave (gamma (0:Axis)) j z*oracle2 1 s t b z j' g (β Γ)) else 0:=by
       let V:= viaP A Γ u i; let K:= viaP A G u i; have h(j:Axis):= stampC (PCAC.Oren.axle true a j) A hA hi u
       have hh(i'): Chart k (foil φ V) 1 ∧ oracle2 1 s t b i' j' g (foil φ V)=(Fintype.card (Site M):ℂ)*oracle2 1 s t b i' j' g (β Γ):=praise A hA hi b s t g 1 u i' j' Γ le_rfl hk hv (m_start a A hA u hi) hY
       have hp: Chart k (foil φ K) 1 := (praise A hA hi b s t g 0 u j j' G le_rfl hk hv (h s) hF).1; apply mul_left_cancel₀ (show μ ≠ 0 from Nat.cast_ne_zero.mpr (Fintype.card_pos).ne'); rw [← (rune A le_rfl G u (h s) hA hi b j j' s t g hv hF hk).2] -- order incorrect. check
       rw [leadT A hA hi a b s t g u hk hp (hh j).1 hv j j' ht]; split
       next h=>
            simp_rw [show ∀ i':Fiber,oracle2 1 s t b i' j' g (F★ Γ)= _ from fun i'=> (hh i').2]; rw [mul_left_comm μ ((r)⁻¹*_ :ℂ)]; simp_rw [mul_sum]; apply sum_congr rfl; intro i _; ring
       next _=>rw [mul_zero]
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.weight1
