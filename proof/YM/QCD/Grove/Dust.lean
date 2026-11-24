import YM.QCD.Grove.Tone
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Trimmings
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Slide Trio.Sharp
-- layout
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
open AnalyticBridge VerifiedReset -- conflicts.
-- currency for raw root sums at every mark. incidence weighted proof needed even flagged. budget P small. 
structure Pockets (T:Finset I)(S:Gem c N I)(B:BudgetPoint)(v d:ℝ): Prop where
    tokenEq: ∃ f:I→ℝ,(∀ i∈T,Woven (S.addr i).site (S.addr i).support B v (S.view i) (f i)) ∧∀ x, ∑ i∈pondC T S x,f i≤ d
variable (S:Gem c N I)(T:Finset I) (h:Pockets T S B t d) (he:0<t)(hk:SoilB T S B w t)(V:Grid c)(x:Site c)
include h he
lemma afloat (x:Site c): let b:=cashD T S (B:=B) V x
            ‖token c N t b‖≤d∧ ‖cloudQ T S (B:=B) x V‖ ≤ d∧0≤ d:=by
    obtain ⟨f,hf,hV⟩:=h.tokenEq; have hh i (hp:i∈T): Sen (S.addr i).site t (letters S B.threshold V i) ≤ f i:=by
         unfold letters; by_cases hi: Healthy B.threshold (S.addr i).support V; · rw [masked_eq _ _ _ _ hi]; exact (hf i hp).sizeU V hi
         rw [masked_ne _ _ _ _ hi, ← measures, map_zero,norm_zero]; exact (hf i hp).travel
    intro b; let p:=pondC T S x; refine ⟨?_,?_⟩
    · unfold b cashD; rw [map_sum]; exact (norm_sum_le ..).trans ((sum_le_sum (fun i hi=>(shot (lens (S.addr i).site) _ _ he).trans (hh _ (mem_filter.mp hi).1))).trans (hV x))
    constructor
    · apply (norm_sum_le _ _ |>.trans ((sum_le_sum ?_).trans (hV x))); intro i hi
      rw [norm_div]; refine le_trans ?_ ((sees (S.addr i).site _ he.le).trans (hh i (mem_filter.mp hi).1)); apply div_le_self (norm_nonneg _); rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]; exact Nat.one_le_cast.mpr (card_pos.mpr ⟨_,(S.addr i).anchor⟩)
    exact (sum_nonneg (fun i hi=> (hf i (mem_filter.mp hi).1).travel)).trans (hV x)
lemma acclaim (i:Site c): ‖crests (cloudQ T S (B:=B)) i V‖ ≤ d:=by
    have ht (s:Strut c): ‖viewS (cloudQ T S (B:=B)) s i V‖≤ d:=(afloat S T h he (Strut.sky s V) _).2.1
    unfold crests; rw [norm_mul]; refine mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun i _=> ht i)) (norm_nonneg _) |>.trans ?_; rw [sum_const,nsmul_eq_mul, card_univ,norm_inv,Real.norm_of_nonneg (by positivity)]; field_simp; rfl -- progress
include hk
lemma inkin (hx:flags B.threshold V=∅): ‖crests (duskQ T S) x V‖ ≤ d:=by
    have he : crests (duskQ T S) x V=crests (cloudQ T S (B:=B)) x V:=by
        unfold crests; congr 1; apply sum_congr rfl; intro i _; symm; apply utter T S hk; unfold Healthy; rw [show flags B.threshold (Strut.sky i V)=∅ from Pane.tranquility (t:=B.threshold) _ hx i.1 i.2]; simp
    rw [he]; exact acclaim S T h ‹0 < t› V x
-- scalar relic leak
section leak
variable {m s q:ℕ}{L:Side}{Y: Stars→Side} (R:∀ i:Stars,(Y i).val=2*(m*Slide.roller i.val)) (F:Stars→Type) (L':∀ i:Stars,Finset (F i))(Z:∀ i, Gem (Y i) N (F i)) (hv:∀ i,SoilB (L' i) (Z i) B w t) (hq:81*m ≤ s)
def duneD (w:ℕ)(d:ℝ):= ∑ i:Stars, |glimmer w i| *((Fintype.card (Site (Y i)):ℝ)*(d+d))
include hv hq
lemma poursK (hi: ∀ i,Pockets (L' i) (Z i) B t d): ‖relic R F L' Z T S x B s V‖≤ d+d + duneD (Y:=Y) m d :=by
    let q i:= crests (duskQ (L' i) (Z i)); let X:=crests (cloudQ T S (B:=B)); let p:= crests (duskQ T S) x 1; let k:= Trio.unearthed B R s (Trio.rip q) x V
    have hx (i:Side) : flags B.threshold (1:Grid i)=∅:=by have he : Healthy B.threshold (@univ (Site i) _) (1:Grid i):= VerifiedReset.flat_ok ..; ext x; simp only [Finset.notMem_empty,iff_false]; exact fun h=>Finset.disjoint_left.mp he (mem_univ _) h
    change ‖X x V-p-k‖ ≤ _; refine (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (acclaim S T h he V x) (inkin S T h he hk (1:Grid c) x (hx _)))) ?_); -- fill args
    · unfold k Trio.unearthed; apply (norm_sum_le ..).trans; refine sum_le_sum fun i _=>?_ ; rw [norm_mul]; refine mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> d+d) (fun j _=> ?_)).trans_eq (by rw [sum_const, card_univ,nsmul_eq_mul]))) (norm_nonneg _)
      let p:= Trio.voyageL R i j x; by_cases hh: Healthy B.threshold (neighbors s p) V; swap; · rw [masked_ne _ _ _ _ hh,norm_zero]; exact add_nonneg (afloat S T h he V x).2.2 (afloat S T h he V x).2.2
      rw [masked_eq _ _ _ _ hh]; change ‖q i j (Slide.shape (Trio.trackR R i) p V)-q i j 1‖≤_; exact (norm_sub_le ..).trans (add_le_add (inkin (Z i) (L' i) (hi i) he (hv i) _ j (Trio.hintQ R s V i hq p hh)) (inkin (Z i) (L' i) (hi i) he (hv i) _ j (hx _)))
omit hv hq h hk he x V
end leak
end YM.QCD.Grove
