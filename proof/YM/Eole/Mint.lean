import YM.Eole.Serene
import YM.Eole.Buds
import YM.Eole.Rate
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
namespace Gain
open QCD.Jets QCD.Jets.Touch QCD Kites Pressure
open ConnectedActivityE6 Reserves Blaze King
open Push.AbsoluteSums.Trees
variable {L0:Side}{v b α:ℝ}
-- enter radius at any chosen fusion level. growth rate o(early meter length) validated later.
noncomputable def youngF (L:Side)(k:ℕ)(x:ℝ): ℝ:= Real.exp (-(28/256:ℝ)*↑((k+k+1:ℕ)^4)) * (taxK L x (1/20))⁻¹ -- ↑ precedence
noncomputable def perchF (L:Side)(x:ℝ): ℝ:= (taxK L x (1/40))⁻¹
noncomputable def soldE (L:Side)(x:ℝ): ℝ:= (taxK L x (1/80))⁻¹
variable (L:Side) (k:ℝ→ℕ)
local notation "U"=> highR L
local notation "V"=> taxK L
local notation "ζ"=> fun i:ℝ=>youngF L (k i) i
local notation "Φ"=>perchF L
local notation "S"=>soldE L
local notation "η"=>(1/2:ℝ)
local notation "p₀"=> (28/256:ℝ)
set_option quotPrecheck false
lemma opens (n:ℕ)(x:ℝ): 0 < youngF L n x:= mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.exp_pos _))
lemma out (n B:ℕ) (x:ℝ): share (youngF L n x) B n (28/256)= (taxK L x (1/20))⁻¹ :=by unfold share youngF; rw [neg_mul, Real.exp_neg]; field_simp
lemma base_rate : Rate su L 0 (fun x=> (highR L x:ℝ)):= (radH L).compare (Eventually.of_forall fun x=> by let d:ℝ:=highR L x; have h:0≤d:=Nat.cast_nonneg _; have hw:1 ≤ (1+d):= le_add_of_nonneg_right h; change |d| ≤ |(1+d)^4|; simp only [abs_of_nonneg h,abs_of_nonneg (show 0≤(1+d)^4 from by positivity)]; exact le_trans (by linarith:d≤1+d) (le_trans (le_of_eq (pow_one (1+d)).symm) (pow_le_pow_right₀ hw (by norm_num))))
lemma degree_rate {v:ℝ→ℝ}(h: Rate su L b v)(δ:ℝ): Rate su L b (fun x=>degreePrice (highR L x) (v x) δ):=by
    have hp :Rate su L 0 (fun x=> ((highR L x+ highR L x+1:ℕ)^4:ℕ)):=by
         push_cast; exact ((((base_rate L).add (base_rate L)).add (Rate.const 1)).pow 4).weaken (by norm_num)
    unfold degreePrice Trees.stretch Animals.ballCost; simp_rw [div_eq_mul_inv]; exact (((hp.mul h).weaken (le_of_eq (zero_add b))).mul_right δ⁻¹).mul_left 4

lemma bill_rate (n m:ℕ)(δ:ℝ): Rate su L 0 (fun i=> rentM (U i) n m δ):=((((base_rate L|>.mul_left 4).add (Rate.const _)).pow (2+m*n)|>.weaken (by ring_nf; try rfl))).mul_right _
variable (f:ℝ→ℝ)
variable (hk:Rate su L 0 fun x=>(k x:ℝ))(hf:Rate su L α f)
include hk hf
lemma minted (n m Fi:ℕ) : ∀ᶠ x:ℝ in atTop, Docket L x (highR L x) n (k x) Fi (youngF L (k x) x) (f x) (perchF L x) (soldE L x) ∧ rentM (highR L x) n m (1/256)*(perchF L x*(1-1/2)⁻¹)≤ soldE L x:=by
    let u:ℝ→ℝ:=Φ; let v:= fun i:ℝ=> ζ i -- notation application.L
    let G x:ℝ:=(taxK L x (1/20))⁻¹; let K x:=Basal.hullP (U x) Fi; let D (x:ℝ):ℝ:=u x*(1-1/2:ℝ)⁻¹; let h(x:ℝ):ℝ:=↑((k x+k x+1)^4:ℕ); have hh:Rate su L 0 h:=by unfold h; push_cast; exact (((hk.add hk).add (Rate.const _)).pow 4).weaken (by ring_nf; try rfl)
    let a':ℝ:=1/256; let b' := rentM
    have hK:Rate su L 0 K:= ((((base_rate L|>.add (base_rate L)).add (Rate.const _)|>.pow 4).mul_right _).weaken (by ring_nf; try rfl))
    have h1 : Rate su L (-1) (fun x=> h x * (u x * f x)+h x*u x):=by
       apply Rate.add; · exact (hh.mul ((couplings (a:=-1-α) L (by norm_num : (0:ℝ)<1/40)).mul hf)).weaken (by linarith)
       exact (hh.mul (show Rate su L (-1) u from couplings L (by norm_num))).weaken (by linarith)
    have hu: Rate su L (-1) u:=couplings L (by norm_num); have hg:Rate su L (-1) G:=couplings L (by norm_num); let e (x:ℝ):ℝ:=S x; let huP :Rate su L (-1) e:=couplings L (by norm_num); have hd:Rate su L (-1) D := hu.mul_right _
    filter_upwards [Basal.bakeAble L,(degree_rate L hu (2/256)).below (by norm_num) (1/2) (by norm_num), (degree_rate L hd (5/256)).below (by norm_num) (1/2) (by norm_num), (hd.mul_right ((1-1/2:ℝ)⁻¹)).below (by norm_num) 1 (by norm_num),hg.below (by norm_num) 1 (by norm_num), (hK.mul hg).below (by norm_num) (14/256) (by norm_num),(h1.mul_right ((2:ℝ)^n)).below (by norm_num) 1 (by norm_num),((bill_rate L n m a').mul (huP.mul_right ((1-1/2:ℝ)⁻¹))).below (by norm_num) 1 (by norm_num)] with x h1 h2 h3 h4 h5 h6 h7 h8
    have hp :0 < u x:=inv_pos.mpr (Real.exp_pos _); have he:0 < e x:=inv_pos.mpr (Real.exp_pos _);
    have hl:u x*u x= G x:=by unfold u perchF G taxK; rw[←mul_inv,←Real.exp_add]; congr 2; ring
    have hh' : e x*e x= u x:=by unfold e soldE u perchF taxK; rw[←mul_inv,←Real.exp_add]; congr 2; ring
    refine ⟨⟨hp,(le_abs_self _).trans h2,(le_abs_self _).trans h3,(le_abs_self _).trans h4,rfl,h1,?_,?_,?_,he⟩,?_⟩ -- shape param muff
    · rw [out]; exact (le_abs_self _).trans h6
    · rw[out]; exact (le_abs_self _).trans h5
    · rw[out,←show u x*u x=(taxK L x (1/20))⁻¹ from hl]; apply le_trans (le_of_eq (show ((↑((k x+k x+1)^4:ℕ):ℝ)*((u x*u x)* f x)+(↑((k x+k x+1)^4:ℕ):ℝ)*(u x*u x))*((2:ℝ)^n)= (h x*(u x*f x)+h x*u x)*2^n * u x from ?_)) -- etc
      · exact (mul_le_mul_of_nonneg_right ((le_abs_self _).trans h7) hp.le).trans_eq (one_mul _)
      unfold h; ring
    apply le_trans (le_of_eq (show rentM (highR L x) n m (1/256)*(Φ x*(1-1/2:ℝ)⁻¹) = (rentM (highR L x) n m (1/256)*(e x*(1-1/2:ℝ)⁻¹))*e x from ?_)); exact (mul_le_mul_of_nonneg_right ((le_abs_self _).trans h8) he.le).trans_eq (one_mul _); change _ = _; rw[←show e x*e x=Φ x from hh']; ring
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.minted
