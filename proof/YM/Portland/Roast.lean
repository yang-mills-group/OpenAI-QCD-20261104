import YM.Portland.Pair
import YM.Massive.Brush.Width
/-! # planes through bilinear at exact weights. Knots orientations independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC.Brave.CoatB
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward Grass.Ovule
open YM.Next.Free QCD.Flume QCD.Globe QCD.Globe.HalfMass Finset NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*}[Fintype A][Fintype B]{c f:Side} {n k j F:ℕ}
variable (x y:Site c)(i j:Lat.Fiber) (a b:Flavor F)
set_option quotPrecheck false
local notation "M"=> Modes c F
local notation "F!"=> Keys c F
noncomputable def aim (i:Lat.Fiber)(a:Flavor F): Site c ↪ Modes c F:= ⟨fun x=> ((x,i),a),fun _ _ h=>congr_arg (fun j:Modes c F=>j.1.1) h⟩
noncomputable abbrev symA (a:Flavor F)(i:Lat.Fiber): Site c ↪ Cove.Keys c F:= (aim i a).trans Embedding.inr
noncomputable abbrev symB (a:Flavor F)(i:Lat.Fiber): Site c ↪ Cove.Keys c F:= (aim i a).trans Embedding.inl
noncomputable def planeL (a:Flavor F)(i:Lat.Fiber): Cove.Keys c F → ℂ:= Grass.Ovule.tint (symA a i) (star ∘ Run.plane)
noncomputable def planeR (a:Flavor F)(i:Lat.Fiber): Cove.Keys c F→ ℂ:= Grass.Ovule.tint (symB a i) Run.plane
noncomputable abbrev talon (a:Flavor F)(i:Lat.Row c): Cove.Keys c F→ℂ:= unitW (Sum.inr (i,a))
noncomputable abbrev graphB (a:Flavor F)(i:Lat.Row c):Cove.Keys c F→ℂ:= unitW (Sum.inl (i,a))
variable (X:Spike)(D: Fields c F)(T:Flavor F→ Sheet c)
-- ordered switch. central_B unnormalized
lemma spinC : (∑ x:Site c,∑ y:Site c, star (Run.plane x)*spinTest X x y (piece a b (traceP D))*Run.plane y) = -∑ i:Lat.Fiber, ∑ j:Lat.Fiber, Lat.wave X j i * Ovule.core _ (spr (planeR b j) (spr (planeL a i) D)):=by
    -- sum reorder
    let H(x y:Site c)(i j:Lat.Fiber):ℂ:= star (Run.plane x)*Run.plane y*Lat.wave X j i * Ovule.core _ (vary ((symB b j) y) (vary ((symA a i) x) D))
    have hp (x y:Site c): star (Run.plane x)*spinTest X x y (piece a b (traceP D))*Run.plane y= - (∑ i:Lat.Fiber,∑ j:Lat.Fiber,H x y i j):=by
         unfold spinTest Matrix.trace; rw [mul_sum, sum_mul]; simp_rw [Matrix.diag_apply,Matrix.mul_apply,mul_sum,sum_mul,← sum_neg_distrib]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
         unfold H; change star (Run.plane x)*(-(Ovule.core _ (vary ((symB b j) y) (vary ((symA a i) x) D)))*(Lat.wave X j i))* Run.plane y= _; ring
    simp_rw [hp, sum_neg_distrib]; apply congr_arg (-·); rw [sum_comm]; -- starts y x i j. want i j y x. use grind sum.
    have hx(i j:Lat.Fiber): Lat.wave X j i * Ovule.core _ (spr (planeR b j) (spr (planeL a i) D))=∑ y,∑ x,H x y i j:=by
         rw [planeR,Ovule.veil, planeL,Ovule.veil]; simp only [map_sum,map_smul,mul_sum, smul_eq_mul]; apply sum_congr rfl; intro y _; apply sum_congr rfl; intro x _; unfold H; rw[comp_apply]; ring
    simp_rw [hx]; -- exchange
    rw [← Fintype.sum_prod_type' (f:=fun y x:Site c=>∑ i:Lat.Fiber, ∑ j,H x y i j), ← Fintype.sum_prod_type' (f:=fun i j:Lat.Fiber=>∑ y,∑ x,H x y i j)]; simp_rw [← Fintype.sum_prod_type']; rw [Fintype.sum_prod_type,Fintype.sum_prod_type (α₁:=Lat.Fiber×Lat.Fiber) (α₂:=Site c × Site c)]; exact sum_comm
local notation "Kq"=> Cove.Keys c F
local notation "BO"=> Ovule.core (Cove.Keys c F)
variable (p q: Lat.Row c)
variable (ht:a≠b) (he: Stew.panel 2 D=form (Matrix.blockDiagonal T))
include he ht
local notation "sι"=> spr (talon b q)
local notation "s²"=> spr (graphB a p)
local notation "sp"=> spr (planeL a i)
local notation "sQ"=> spr (planeR b j)
lemma braidF : BO (s² (sι D))=0:=by
    change Ovule.core _ (spr (unitW (A:=Pairs (Modes c F)) (.inl (p,a))) (spr (unitW (.inr (q,b))) D))=_; rw [unitV,unitV,readB _ _ D (Matrix.blockDiagonal T) he, Matrix.blockDiagonal_apply]; simp [ht.symm]
lemma braidC : BO (sQ (sp D))=0:=by
    rw [planeL, planeR,Ovule.veil,Ovule.veil,map_sum]; apply sum_eq_zero; intro x _; rw [map_smul,map_sum] -- order
    simp only [map_smul,map_sum,smul_eq_mul]; rw [sum_eq_zero,mul_zero]; intro y _; change _*BO (vary (Sum.inl _) (vary (Sum.inr _) D))= _; rw [readB _ _ D (Matrix.blockDiagonal T) he,Matrix.blockDiagonal_apply]; simp[aim,ht]
-- ordering with pair (i,j) source from fun talon and graphB.
omit ht
lemma braidA : BO (sp (sι D))=0:=by
    unfold talon; rw [unitV,planeL,Ovule.veil,map_sum]; apply sum_eq_zero; intro x _; rw [map_smul]; change _ • Ovule.core _ (vary (X:=Pairs (Modes c F)) (.inr _) (vary (.inr _) D))=_; rw [missV _ _ D _ he,smul_zero]
lemma braidB : BO (sQ (s² D))=0:=by
    unfold graphB; rw [unitV,planeR,Ovule.veil,map_sum]; apply sum_eq_zero; intro x _; rw [map_smul]; change _ • Ovule.core _ (vary (X:=Pairs (Modes c F)) (.inl _) (vary (.inl _) D))=_; rw [missB _ _ D _ he,smul_zero]
local notation "Wp"=> Run.plane
lemma abroad : ‖BO (sQ (sι D))‖ ≤ ‖stalk (T b) q.1‖:=by
    have h: star (Run.plane q.1)*BO (sQ (sι D))= -(stalk (T b) q.1 q.2 j):=by
        unfold stalk cashRow talon; rw [unitV,planeR,Ovule.veil,map_sum,mul_sum,Matrix.sum_apply,← sum_neg_distrib]; apply sum_congr rfl; intro y _; rw[map_smul,Matrix.smul_apply]; change star _*(Run.plane y* BO (vary (.inl ((y,j),b)) (vary (.inr _) D)))= _; rw [readB _ _ _ _ he,Matrix.blockDiagonal_apply]; change _*(Run.plane y* - (if b=b then _ else 0)) =-(_*((T b) (q.1,q.2) (y,j))); rw [if_pos rfl]; unfold pCoin; rw [Prod.eta]; ring
    apply le_trans (b:= ‖stalk (T b) q.1 q.2 j‖); · rw [← neg_le_neg_iff]; apply le_of_eq; apply congr_arg; rw [← norm_neg (stalk (T b) q.1 q.2 j),← h,norm_mul,norm_star,plane_cost,one_mul]
    exact Cost.north ..
lemma ahead : ‖BO (sp (s² D))‖ ≤ ‖ringP (T a) p.1‖:=by
    have h: Run.plane p.1 *BO (sp (s² D))= ringP (T a) p.1 i p.2:=by
        unfold ringP graphB; rw [unitV,planeL,Ovule.veil,map_sum,mul_sum,Matrix.sum_apply]; apply sum_congr rfl; intro x _; rw[map_smul,Matrix.smul_apply]
        change Run.plane p.1 * (star (Run.plane x)* BO (vary (.inr ((x,i),a)) (vary (.inl (p,a)) D)))=_; rw [readL _ _ _ _ he,Matrix.blockDiagonal_apply]; change _ * (_ * (if a=a then _ else 0))= pCoin x p.1*(T a (x,i) p); rw [if_pos rfl]; unfold pCoin; ring
    apply le_trans (b:=‖ringP (T a) p.1 i p.2‖); · rw [←h,norm_mul,plane_cost,one_mul]
    exact Cost.north ..
end YM.Massive.PCAC.Brave.CoatB
#print axioms YM.Massive.PCAC.Brave.CoatB.ahead
