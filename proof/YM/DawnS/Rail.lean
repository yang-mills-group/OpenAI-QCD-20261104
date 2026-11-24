import YM.DawnS.Tray
import YM.DawnS.Nettle
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder
variable {d:ℕ}(r:ℝ)(hr:0<r)
local notation "I₀"=> Vault d
local notation "wd"=>fun _ : Fin 2 =>d
local notation "Q"=> chime (fun _ : Fin 2=>d) (dotsG r)
local notation "QZ"=>unionB Q
local notation "K"=> timeAxis
open Maxwell.Free
local notation "A"=> Signed.reflect timeAxis
set_option quotPrecheck false
set_option maxHeartbeats 810000
local notation "Gτ"=> ((Labels.rotated A).toLinearMap.comp conjGPol)
lemma gaugeC (p:GPol): Maxwell.reduceEq ((Gτ) p)=mirrorBar (G:=su) A (Maxwell.reduceEq p):=by
     apply Maxwell.equalPol; intro t; change Maxwell.probe t (Maxwell.reduceEq (Labels.rotated A (Labels.conjPol _)))= Maxwell.probe t (reflectPol A (realForm _))
     rw [jet_value,reflects_eval,real_eval,jet_value, Labels.rotated,Labels.eval_changed, Labels.conj_value]; congr 3; funext i; exact gauge_orient A⁻¹ _
lemma intertwine (P:Pol d) (ξ:scarG d→ₗ[ℂ]beam d)(hξ:(slashEq d).mkQ.comp ξ=LinearMap.id): let Kξ:=TensorProduct.map (Elm.draw su).toLinearMap (ExteriorAlgebra.map ξ).toLinearMap; UV.Free.reduceEq (UV.adj timeAxis P)= UV.Free.reduceEq (UV.adj timeAxis (Kξ (UV.Free.reduceEq P))):=by
     intro U; induction P using TensorProduct.induction_on with
     | zero=>simp
     | add x y hx hy=>simp only [map_add,hx,hy]
     | tmul x y=> simp only[UV.Free.reduceEq, U, TensorProduct.map_tmul,UV.adj]; simp only[AlgHom.toLinearMap_apply]; change Maxwell.reduceEq ((Gτ) x) ⊗ₜ[ℂ] bareT d (τSpin d y)= Maxwell.reduceEq ((Gτ) ((Elm.draw su) (Maxwell.reduceEq x))) ⊗ₜ[ℂ] bareT d (τSpin d (ExteriorAlgebra.map ξ (bareT d y))); rw[gaugeC,gaugeC, planted, ←τSpin_ltr y ξ hξ]
lemma intertwineEq(x y: Pol d) (h:UV.Free.reduceEq x= UV.Free.reduceEq y):UV.Free.reduceEq (UV.adj timeAxis x)=UV.Free.reduceEq (UV.adj timeAxis y):=by
     obtain ⟨ξ,H⟩:= (slashEq d).mkQ.exists_rightInverse_of_surjective (slashEq d).range_mkQ; refine (intertwine x ξ H).trans ?_; exact Eq.trans (congr_arg _ (congr_arg _ (congr_arg _ h))) (intertwine y ξ H).symm
include hr
lemma detectsG (p q: WickPol su): Wick.moment su (dotsG r) ![mirrorBar A p,q] = score K (prelude (r/2)) p q:=by
    let z:=prelude (r/2); let Z := points fun _ : Fin 1=> z; let s:=Table.Pairing.closedUp timeAxis Z Z
    change _=Wick.moment su s _; rw[← Maxwell.Free.moment_across s _ z]
    have he : dotsG r=Points.across z s:=by
         ext1 i; refine Fin.addCases (m:=1) (n:=1) ?_ (fun i=>?_) i
         · intro i; change dotsG r (Fin.castAdd 1 i)=(s (Fin.castAdd 1 i))+_;
           unfold s; rw[Table.Pairing.enter]; fin_cases i; change (0:E4)= through K z+z; rw [show through K z=-z from ?_,neg_add_cancel]; apply PiLp.ext; intro k; by_cases h:k=K <;> simp[through,h,z,prelude]
         change dotsG r (Fin.natAdd 1 i)= (s (Fin.natAdd 1 i))+_; unfold s; rw[Table.Pairing.leave]; fin_cases i; change prelude r=z+z; unfold z prelude; rw [←add_smul,add_halves]
    rw [he]; congr 1; ext1 i; fin_cases i <;> rfl
end YM.DawnS
