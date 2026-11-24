import YM.Massive.Brush.Snow
/-! Plane quadratic propagation estimate in `E-bias`. Use the
same plane for both ends, cancellation before charging. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
namespace Brave
open Finset NormedSpace Loft Globe.HalfMass QCD.Globe QCD.Revolve
open MeasureTheory
open scoped Kronecker
variable (a b:Flavor F)(X:Spike)
local notation "T"=> onSpin
local notation "d"=> (Fintype.card Lat.Fiber:ℝ)
local notation "S"=> (Fintype.card (Site c):ℝ)
local notation "g"=> Lat.g5
local notation "p"=> Run.plane
local notation "Y"=> flavorW g5 a b c
local notation "cell"=> QCD.Run.cell
noncomputable def pCoin (i j:Site c):ℂ:= star (p i)*p j
lemma chive (i j k:Site c): pCoin i j * pCoin j k=pCoin i k:=by
    have hp: p j*star (p j)=1:=by rw [show p j*star (p j)=_ from Complex.mul_conj' _, plane_cost j]; norm_num
    unfold pCoin; rw [mul_assoc,← mul_assoc (p j),hp,one_mul]
lemma chive_star (i j:Site c): star (pCoin i j) = pCoin j i:=by rw [pCoin,star_mul,star_star]; rfl
noncomputable abbrev stalk (W:Sheet c)(i:Site c) := cashRow W pCoin i -- arg order from Half? w o after
noncomputable def ringP (W:Sheet c)(i:Site c):Bundle:= ∑ j: Site c,pCoin j i • cell W j i
-- chiral swap provides column estimate from row (no approximation)
private lemma ridden(W:Sheet c)(h:Tempo W)(i j:Site c) : cell W i j= wave g *star (cell W j i)*wave g:=by
    obtain he:=h.song; unfold newborn aura at he; nth_rw 1 [← he];
    unfold chirality onSpin; rw [Bay.cell_ride_right,Bay.cell_ride_left,Equiv.refl_apply]; simp only [wave_star,g5_star]; rfl
lemma ring_l (W:Sheet c)(h:Tempo W)(i:Site c) : ringP W i= (wave g)*star (stalk W i)*(wave g):=by
    unfold ringP stalk cashRow; rw [star_sum,Matrix.mul_sum,Matrix.sum_mul]; apply sum_congr rfl; intro j _; rw [star_smul,chive_star,ridden W h j i,Matrix.mul_smul,Matrix.smul_mul] -- watch order
lemma ring_cost (W:Sheet c)(h:Tempo W)(i:Site c): ‖ringP W i‖ ≤ spinPrice g * ‖stalk W i‖ * spinPrice g:=by rw [ring_l W h]; exact (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_right (norm_mul_le ..) (norm_nonneg (wave g))).trans_eq (by unfold spinPrice; rw [norm_star]))
local notation "β"=> pCoin
-- momentum at leading $M W M$.Use F all, a,b diff for trace but sources as below.
lemma basic_mul (A B:Sheet c)(i j:Site c): cell (A*T c X*B) i j= ∑ r:Site c, cell A i r *Lat.wave X * cell B r j :=by
    rw [mul_assoc, QCD.Run.cell_mul]; unfold onSpin; simp_rw [Bay.cell_ride_left]; apply sum_congr rfl; intro s _; exact (mul_assoc ..).symm
lemma compose (A B:Sheet c):
    let J:=Fintype.card (Site c)*Fintype.card Lat.Fiber
    (J:ℂ)*artPrice X (A*T c X*B)=∑ z:Site c, ((ringP A z* Lat.wave X * stalk B z)*Lat.wave X).trace:=by
    intro n; have hK:(↑(Fintype.card (Site c)*Fintype.card Lat.Fiber):ℂ)≠0:=by positivity
    let f(i j z: Site c):= ((cell A i z * Lat.wave X *cell B z j)*Lat.wave X).trace
    unfold artPrice; dsimp only [n]; rw [← Nat.cast_mul,mul_div_cancel₀ _ hK];
    have hp (i j): star (Run.plane i)* spinTest X i j (A*T c X*B) * Run.plane j=∑ z:Site c,pCoin i j * f i j z:=by unfold spinTest; rw [basic_mul,Matrix.sum_mul, Matrix.trace_sum,mul_sum,sum_mul]; unfold f pCoin; apply sum_congr rfl; intro k _; ring
    have hs(z:Site c): ∑ i:Site c,∑ j:Site c,pCoin i j * f i j z = ((ringP A z* Lat.wave X* stalk B z)*Lat.wave X).trace:=by
         unfold ringP stalk cashRow; simp_rw [Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]; unfold f; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [←chive i z j]; simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,smul_eq_mul]; ring
    simp_rw [hp,←hs]; rw [← Fintype.sum_prod_type' (f:=fun i j=>∑ z:Site c,pCoin i j*f i j z),sum_comm]; apply sum_congr rfl; intro a _; rw [Fintype.sum_prod_type]
lemma trace_cost (X: Bundle) : ‖X.trace‖ ≤ d*‖X‖ := by unfold Matrix.trace; apply (norm_sum_le ..).trans; exact (sum_le_sum (s:=(univ:Finset Lat.Fiber)) («g»:=fun _=> ‖X‖) (fun i _=> Cost.north X i i)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])
noncomputable def productTariff (X:Spike) :ℝ:= spinPrice g * spinPrice X * spinPrice X * spinPrice g
lemma coinTariff :0≤ productTariff X:=by unfold productTariff; have h:= spinPrice_nn X; have hg:=spinPrice_nn g; positivity
lemma summer (A B: Sheet c)(h:Tempo A)(C:ℝ)(hx:0≤ C)(hv:∀ i,‖stalk A i‖ ≤ C)(hu:∀ i,‖stalk B i‖ ≤ C) : ‖artPrice X (A*(T c X)*B)‖≤ productTariff X * C^2:=by
    obtain θ:= compose X A B; let s:=spinPrice g; let t:=spinPrice X; have hs:0≤ s:=spinPrice_nn g; have ht:0≤t:=spinPrice_nn X; let v:= Fintype.card (Site c)*Fintype.card Lat.Fiber; let E(i:Site c):= ((ringP A i*wave X* stalk B i)*wave X).trace; let f:= productTariff X*C^2
    have hp (i:Site c):‖E i‖≤ d*f:=by
        have hi : ‖ringP A i‖ ≤ s*C*s:= (ring_cost A h i).trans (by gcongr; exact hv _)
        apply (trace_cost _).trans; apply mul_le_mul_of_nonneg_left _ (by positivity); apply (norm_mul_le ..).trans
        have hh(z:Bundle): ‖z * Lat.wave X‖ ≤ ‖z‖*t:= norm_mul_le ..
        apply le_trans (b:=(s*C*s*t*C)*t) _ (le_of_eq ?_); swap
        · unfold f productTariff; unfold t s; ring
        exact mul_le_mul_of_nonneg_right ((norm_mul_le ..).trans (mul_le_mul ((hh _).trans (mul_le_mul_of_nonneg_right hi ht)) (hu i) (norm_nonneg _) (by positivity))) ht
    have hV:0<(v:ℝ):=by unfold v; positivity
    apply le_of_mul_le_mul_left _ hV; rw [← Complex.norm_natCast v, ← norm_mul, show (v:ℂ)*artPrice X _=∑ i:Site c,E i from θ]; refine (norm_sum_le ..).trans ((sum_le_sum fun i _=>hp i).trans_eq ?_); rw [Complex.norm_natCast,sum_const,card_univ,nsmul_eq_mul]; unfold v f; push_cast; ring -- norm_natCast also RHS
end Brave
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.Brave.summer
