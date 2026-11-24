import YM.MassiveQCD.Plate.Coupons
import YM.MassiveQCD.Cupola.Garden
/-! # Through-regularity metrics and relative-exponent carrier -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{m k B N:ℕ}{s t h a r η σ φ θ:ℝ}{P:BudgetPoint}{J D I E:Type}[Fintype I]
local notation "Z"=> Keys c N
-- Upper moment metric.Movable.Stated in real scalar orientation.W cost factor after Flag projection.
noncomputable def toll (O:Site c)(k:ℕ)(s:Finset (Keys c N))(t:ℝ):ℝ:= (1+  (↑(s.sup (Stew.lens O)):ℝ))^k * t^s.card
noncomputable def view (O:Site c)(k:ℕ)(v:Alg (Keys c N))(t:ℝ):ℝ:=∑ s:Finset Z,toll O k s t * ‖coef s v‖
lemma view_nn (O:Site c)(x:Alg (Keys c N))(t:ℝ)(hf:0 ≤t): 0≤view O k x t := sum_nonneg fun i _=>mul_nonneg (by unfold toll; positivity) (norm_nonneg _)
lemma viewSen (O:Site c)(x:Alg (Keys c N))(t:ℝ)(hf:0≤t): view O 2 x t=Stew.plank O t x:= by unfold view Stew.plank; rw [pricesD _ hf]; refine sum_congr rfl fun i _=>?_ ; unfold toll starch pieD; push_cast; rfl -- linter
lemma viewer (O:Site c)(x:Alg Z)(k:ℕ)(ht:0<t): Creek.load (fun _=>t) x ≤ view O k x t:=by rw [dry _ (fun _=>ht)]; apply sum_le_sum; intro i _; rw [prod_const]; unfold toll; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by simp))
lemma rangeView (O:Site c)(x:Alg Z)(k:ℕ)(ht:0<t)(S:Support c)(hp:x∈region (limits S))(hO:O∈ S): view O k x t ≤ (1+(ConnectedActivityE6.Blaze.King.wag S B:ℝ))^k*Creek.load (fun _=>t) x:=by
    rw [dry _ (fun _=> ht), mul_sum]; apply sum_le_sum; intro i _; unfold toll; rw [prod_const]
    by_cases he:i⊆limits S; swap; · rw [soil _ _ _ hp he,norm_zero,mul_zero,mul_zero,mul_zero]
    have hh:i.sup (Stew.lens O) ≤ ConnectedActivityE6.Blaze.King.wag S B:=Finset.sup_le fun j hj=> Corona.extent _ _ ((mem_filter.mp (he hj)).2) hO
    rw [← mul_assoc]; gcongr
lemma changeView (O:Site c)(x:Alg Z)(k:ℕ)(_h:0≤t)(hh:0≤a): view O k (engine a Z x) t=view O k x (a*t):=by
    unfold view; refine sum_congr rfl fun i _=>?_ ; rw [fundW,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hh]; unfold toll; rw [mul_pow]; ring -- lint t
lemma birthView (O:Site c)(v:Alg (Keys c N))(k:ℕ)(h:0≤ t)(hp:t ≤ a): view O k v t ≤ view O k v a:=by apply sum_le_sum; intro i _; unfold toll; gcongr
-- publishing E no length produced by closure until underlying Sense of gauge norm
structure Sight (v:Support c)(o:Site c)(k:ℕ)(P:BudgetPoint)(t:ℝ)(F:Grid c→ Alg (Keys c N))(a:ℝ):Prop where
   room : LocalOn v F
   gate i:F i∈region (limits v)
   use (V):Healthy P.threshold v V→ Push.Local.Chart P.order F V
   pole :∀ V,Healthy P.threshold v V→∀ l,List.length l≤P.order→(∀ i∈l,P.dirBound o i)→ view o k (RG.leftDerivs F l V) t ≤ a
   borel: Measurable F
   travels :0 ≤ a
-- regular Sky
variable (p :I→Site c)(q:I→Bool)
structure Reel (c:Side)(N:ℕ)(I D:Type)[Fintype I] where
    addr:D→RegularAddress c
    z:D→Finset I
    mark: D→Grid c→ Stitch.Tine c N I
variable {X: Support c}{o: Site c}
namespace Reel
structure Book (Y:Reel c N I D) : Prop where
    stays i:(Y.z i).Nonempty
    stamp i:(Y.z i).image p⊆(Y.addr i).support
    permit i:Measurable (Y.mark i)
    room i:LocalOn (Y.addr i).support (Y.mark i)
    stage i U: Stitch.lights (Y.z i) (Y.addr i).support p q (Y.mark i U)
    tint i U g: parcelColor N g I (Y.mark i (Lattice.gauge g U))= Y.mark i U
-- geometric inhabit.Step posting φ lengths from any assigned beam.A including global units not booked.
noncomputable def speaker (Y:Reel c N I D)(u:D)(V:Grid c):= pluck (Keys c N) (burst q (Y.z u)) (Y.mark u V)
noncomputable def mist (Y:Reel c N I D)(t:ℝ)(i:D)(U:Grid c):= masked t (Y.addr i).support (Y.mark i) U
noncomputable def rope (Y:Reel c N I D)(t:ℝ)(U:Grid c):=∑' i,mist Y t i U
structure Occupant (Y: Reel c N I D)(p:I→Site c)(q:I→ Bool)(v:ℝ)(P:BudgetPoint)(k:ℕ)(α δ:ℝ)(w:I→ℝ) :Prop where
    booked : Y.Book p q -- argument order Book p q Y; field projection?
    reserve : ∃ f:D→ℝ, Ac.Hit (fun i=>(Y.addr i).support) P.B (fun i=>(∏ j∈(Y.z i),|w j|)*f i) α δ ∧ ∀ i, ∀ j∈ Y.z i,Sight (Y.addr i).support (p j) k P v (speaker q Y i) (f i)
-- Fractal.N.Mark.Ke
end Reel
open ConnectedActivityE6 Blaze King
variable (s:Finset I)(p:I→Site c)(q:I→Bool)(φ:ℝ)(F:Grid c→ EvenA c (ample N I))
local notation "R"=> Spine I
local notation "mx"=> Keys c N⊕Spine I
local notation "M"=> Ribbon.ample N I
local notation "η"=> withdraw N p φ
local notation "wbr"=> fun U=> turn I t (η (F U))
lemma derivMints (l:List (Directions su c))(hm:0<φ)(X: RegularAddress c)(h:Woven X.site X.support P φ F a)(hr:∀ i,Mint N p φ q s (F i))(V:Grid c)(hl:l.length ≤ P.order)(hv:Healthy P.threshold X.support V): Mint N p φ q s (leftDerivs F l V):=by
   let A:= trophy N p φ q {s}; apply (Mint.gauge hm).mpr; change A _ = _; rw [← left_linear A _ (h.use V hv) hl]; rw [show A ∘ F= F from funext fun i=> (Mint.gauge hm).1 (hr i)]
-- Weigh PRINCIPAL at increased moment frequency afterward. Need Woven at every billed marker root.w. Applies unmarked tape arc (orientation cost) without dimension count.
lemma invoice (X:RegularAddress c)(hφ:0<φ)(h:Woven X.site X.support P φ F a)(hξ:∀ i,Mint N p φ q s (F i))(ht:0<t)(hv:0<θ)(hp:t*θ ≤ φ) (m:ℕ): Sight X.support X.site m P θ (fun U:Grid c=>pluck Z (burst q s) (turn I t (withdraw N p φ (F U)))) ((1+(wag X.support P.B:ℝ))^m*a):=by
   let G:= η; let v:=G.toLinearMap.toContinuousLinearMap; let q' := turn I (D:=Z) t; let w:= (pluck Z (burst q s)); let L:= ((w.comp q'.toLinearMap.toContinuousLinearMap).comp v).restrictScalars ℝ
   change Sight _ _ _ P θ (L∘F) _; refine ⟨fun i U he=>congr_arg L (h.room i U he),?_,fun V hv=> L.contDiff.contDiffAt.comp 0 (h.use V hv),?_,L.measurable.comp h.Borel,mul_nonneg (by positivity) h.travel⟩
   · intro i; change pluck _ _ (turn I t _) ∈_; rw [turned]; exact hopeful N t _ _ (pennied N p φ (burst q s) (F i) _ (h.gated i)) -- hopeful arguments
   intro V hx l hl hL; let v:= leftDerivs F l V; let f:=w (G v); rw [Push.Local.left_linear L l (h.use V hx) hl]; change view _ _ (w (turn I t (η v))) _ ≤_
   rw [show w (turn I t (η v))=engine t Z f from turned ..]; rw [changeView X.site f m hv.le ht.le]; refine (birthView X.site f m (mul_pos ht hv).le hp).trans ((rangeView X.site f m hφ X.support (pennied N p φ _ v X.support (King.gatedL h.gated l V)) X.anchor).trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
   exact ((derivMints s p q φ F l hφ X h hξ V hl hx).launch.pin _ hφ).trans ((shot (Stew.lens (N:=M) X.site) v.val φ hφ).trans (h.pole V hx l hl hL)) -- order funding
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.invoice
