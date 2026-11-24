import YM.Tinus.RollerB
import YM.Pods.Typing
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A:Type*}[Fintype A] {c f:Side}{j k F:ℕ}
open Finset
open Patria Patria.Depth Patria.Rolls
variable {S:Scheme} {i m n:ℕ} {R:Side} (A:Run S n R 6) (X:Spike)(x y:Flavor 6)(q:Bool)
local notation "Y"=> film X x y A q m
local notation "W"=> S.side R
variable (t: Massive.Patria.Rolls.Sail)
local notation "G"=> stalk X A x y q m
local notation "Hm"=> ratioTo S m i
lemma whole_ax (h:i ≤ m):
     ∑ j:Site (S.side R i), Depth.report A G (.some t) i (Lattice.lift j)=(((ratioTo S m i:ℕ):ℝ)^4)⁻¹ • S.toStop R A.β A.w m i (film X x y A q m):=by
      let f(k:Site (S.side R m)):Insertion (W m) 6:=mark q (localF k X x y) (actor A m); let T:=A; let g(b:Cover):= stalk X T x y q m b
      have hp:∑ k:Site (W m), f k= (film X x y A q m):=ContinuousMap.ext fun V=>by rw [ContinuousMap.sum_apply]; exact mark_collect x y X q _ _
      have he:∑ j :Site (W i), Averaging.filter (.some t) (Hm) g ((Hm) • Lattice.lift j)=(( (ratioTo S m i:ℕ) :ℝ)^4)⁻¹ • film X x y A q m:= Eq.trans (harmonyR (Hub.viewW S R h) f (odd_to h) t) (congr_arg _ hp)
      let D:= S.toStop R A.β A.w m i (F:=6)
      calc
           ∑ j:Site (W i), Depth.report A G (.some t) i (lift j)= D (∑ j:Site (W i),Averaging.filter (.some t) Hm g (Hm • lift j)):= (map_sum D (fun j:Site (W i)=>Averaging.filter (.some t) Hm g (Hm • lift j)) univ).symm
           _=_:= by rw [he]; exact map_smul (D.restrictScalars ℝ) _ _
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.whole_ax
