import YM.Oriole.Visee
import YM.Oriole.Tree
/-! Spatial central differences translation. Due specifically at STEP 0 relative.Taper dot.Jet.W.Meta. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG Wilson
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d n:ℕ}{a b:Flavor 6}{g:Bool}{c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder
local notation "T"=> Lat.Fiber
variable (P X:Density c 6)(u v:Site c)(i j: Axis)(x:Cover)
local notation "W"=>Patria.march x
local notation "U"=> Kit.disguise (c:=c) -- likely no arg
local notation "φ"=> Canvas.foil P X
open QCD.Entr.Goals
open TorusPCAC.Ward Grass.Ward
local notation "κ"=> heat (n:=c) x
local notation "t"=> wrap c x
local notation "ι"=>Canvas.foil P (Patria.march x X)
-- P unit globally not needed
lemma ambassador (he:IsUnit (P 1))(ht: W P = P) : Canvas.foil P (Patria.march x X) 1= Patria.march x (Canvas.foil P X) 1:=by
      let V:= crank (N:=6) 1 1 t κ; have hp : pull (K:=su.El) 1 t (1:Grid c) = 1:=funext fun _=>by simp [pull,Step.read]
      have hv:V (P 1)=P 1:=by have hf:=congr_fun ht 1; unfold Patria.march post at hf; rw [hp] at hf; exact hf
      unfold Patria.march post; simp only [Canvas.foil]; rw[hp]; change _= V _; have hX:= (Ring.inverse_mul_eq_iff_eq_mul (P 1) (V (X 1)) (V (Canvas.foil P X 1)) he); apply hX.mpr
      nth_rw 1 [← hv]; rw [← map_mul]; apply congr_arg; exact Eq.symm (Ring.mul_inverse_cancel_left _ _ he) -- hp
local notation "M0" p:arg => piece a b (uncoat p)
-- exact stencil shift in raw real ambient.
set_option maxHeartbeats 650000
lemma thug : let T':= (M0 (X 1)); let G:= (M0 (Patria.march x X 1)); QCD.Run.cell G (u+t) (v+t)= (κ u*κ v) • QCD.Run.cell T' u v :=by
      intro T' G; let H:= glares (n:=c) x; let A := hues t 1 κ 1; let M:= Lat.copies 6 A; have ha:A∈unitary _:=colour_wheel H Swing.none; have he : W X 1= Kit.disguise M (X 1):=by
           change Kit.disguise M (X (pull 1 t 1))=_; rw [show pull (K:=su.El) 1 t (1:Grid c)=1 from funext fun i=>by simp [pull,Step.read]]
      have hG : G =star A*T'*A :=by unfold G; rw [he,Kit.disguise,sectX,Matrix.transpose_transpose, ← Lat.copies_star, angel,angie, ← mul_assoc]; -- M let
      have hx:A*G*star A=T':=by rw [hG,← mul_assoc,← mul_assoc,ha.2, one_mul,mul_assoc,ha.2,mul_one]
      rw [← hx]; unfold A hues; rw [QCD.Bay.cell_ride_right, QCD.Bay.cell_ride_left]; have ht(i:Site c): shiftE 1 t i=i+t:=by simp [shiftE,Signed.actEquiv];
      rw [ht,ht]; rcases H.sign u with h|h<;> rcases H.sign v with h1|h1<;>rw [h,h1]<;> simp [wave_one]
-- Direction shape bounds. Compare Np shift to exact inside; outside pay O((rad+1)^2/c).
variable (H:Taper)(Z:ℝ)
local notation "I"=> (0:Multi 8)
local notation "L"=> UV.first
local notation "F"=> fun u=> Nw H (UV.first j) u
local notation "Xc" s:arg=> Lattice.lift s
local notation "μ" i:arg=> pdist i
local notation "ξ" u:arg=> Np H u
lemma charts(hx:∀ a:Axis,Int.natAbs (x a) ≤ 1)(hp:8*(pdist u+2) < c.val): ξ u=Massive.Cylinder.ap c (Lattice.lift u) ∧ Lattice.lift (u+t) = Lattice.lift u+x ∧ κ u * ξ (u+t)=Massive.Cylinder.ap c (Lattice.lift u):=by
     let f := H.χ; let T':= Lattice.lift u; let r:= u+t
     have hz : Lattice.lift r=T'+x:=lift_eq_iff.mpr ⟨by simp only[map_add,T',wrap_lift]; rfl,fun i=>by have hp0: Int.natAbs ((T'+x) i)≤ μ u+1:=(Int.natAbs_add_le (T' i) (x i)).trans (Nat.add_le_add (component_le u i) (hx i)); omega⟩
     have hh(y:Cover)(ht:∀ i: Axis, Int.natAbs (y i) ≤ μ u +1) : H.χ ((c.val:ℝ)⁻¹ • vector y)=1:=by
           apply H.near; intro i; change |(c.val:ℝ)⁻¹ * (y i:ℝ)|≤_; rw[abs_mul,abs_of_nonneg (by positivity),mul_comm,←div_eq_mul_inv,div_le_iff₀ (by positivity),←Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast]; have he: Int.natAbs (y i)*8 ≤ c.val:=by have h:= ht i; omega
           push_cast; have h:((Int.natAbs (y i)):ℝ)*8 ≤  (c.val:ℝ):=by exact_mod_cast he
           linarith
     refine ⟨?_,hz,?_⟩
     · unfold Np; rw[hh,Complex.ofReal_one,one_mul]; exact fun i=>(component_le ..).trans (Nat.le_succ _)
     have hT: ξ (u+t)=ap c (Xc u+x):=by unfold Np; rw[hz,hh,Complex.ofReal_one,one_mul]; exact fun i=> (Int.natAbs_add_le (T' i) (x i)).trans (Nat.add_le_add (component_le u i) (hx i))
     have hQ:= heated (n:=c) x (Lattice.lift u); rw [wrap_lift] at hQ; rw [hT]; rw [show ap c _=_ from (show ap c (Lattice.lift u+x)= κ u*ap c _ from hQ),←mul_assoc, show κ u*κ u=1 from thermal_norm _, one_mul]
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.ambassador
#print axioms YM.Massive.Oriole.thug
#print axioms YM.Massive.Oriole.charts
