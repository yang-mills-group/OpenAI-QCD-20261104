import YM.MassiveQCD.Festival.Park
import YM.QCD.Finch.Trust
/-! # Colored Charge interfaces for re-expression after mass accounting
 Must enter `Hill` Step at coarser tick, carrying genuine all-power budgets & reflection masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Relight
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ} {a r u t σ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Festival
structure Wax (Y: Ruby.Hue c N I)(u:ℝ)(b:ℕ)(v a t:ℝ) :Prop where
   burns : Y.Tall u
   expense : ∃ f:I→ℝ,Ac.Hit Y.bud b f v a ∧∀ i U, ‖token c N t (Y.mean i U)‖ ≤ f i
structure LampInk (Y:Ruby.Hue c N I) :Prop where
   gauge i : shadeG (Y.mean i)
   real i U: Regal c N (Y.mean i U)=Y.mean i U
   fit i U: AccentFit (Y.mean i U)
structure Yank (Y:Ruby.Hue c N I)(p:I→ℕ) :Prop extends LampInk Y where
   glamour s k g: Warrant s g k→∃ e:Equiv.Perm I, Got Y.bud e (act s)∧ (∀ i: I,p (e i)=p i) ∧∀ (i: I) (U: Grid c), Diode N s k g (Y.mean i (sky s U))=Y.mean (e i) U
variable (Y:Ruby.Hue c N I)(X:Gem c N I) (v:I→ℕ) (s:ℕ→ℂ)
local notation "K"=>EvenA c N
lemma reach_w {Y:Ruby.Hue c N I}{Z: Ruby.Hue c N J}(h:Wax Y u p.B t η a)(he:Wax Z u p.B t r a): Wax (Ruby.HJoin Y Z) u p.B t (η+r) a:=by
   obtain ⟨f,hf,hV⟩:=h.expense; obtain ⟨g,hg,hW⟩:=he.expense; refine ⟨Ruby.branche _ _ h.burns he.burns, Sum.elim f g,fun i=> Extra.Iteration.Cost.sum (hf i) (hg i),?_⟩; intro i; rcases i with i|i; exact hV _; exact hW _
lemma notedW {Y:Ruby.Hue c N I}{Z:Ruby.Hue c N J}(v:I→ℕ)(w:J→ℕ)(h:Yank Y v)(he:Yank Z w): Yank (Ruby.HJoin Y Z) (Sum.elim v w):=by
    constructor
    · constructor <;> rintro (i|i) <;> first| exact h.fit i| exact he.fit i | exact h.real i| exact he.real i| exact h.gauge i | exact he.gauge i
    intro s k g hp; obtain ⟨e,h,hX,hY⟩:= h.glamour _ _ _ hp; obtain ⟨d,h',hX',hY'⟩:=he.glamour _ _ _ hp
    exact ⟨Equiv.sumCongr e d,(fun i=> by rcases i with i|i; exact h i; exact h' i), (fun i=> by rcases i with i|i; exact hX i; exact hX' i), fun i U=> by rcases i with i|i; exact hY i U; exact hY' i U⟩
lemma Wax.heated {Y:Ruby.Hue c N I}(h:Wax Y u p.B t η a)(he:1 ≤ a)(hr:0≤t)(x:Grid c): Summable (fun i=>Y.mean i x) ∧ Summable (fun i=> ‖Ruby.sparkY Y x i‖):= by obtain ⟨f,hf,hV⟩:=h.expense; exact Ruby.hearts Y h.burns hf (fun i=>(norm_nonneg _).trans (hV i 1)) he hr hV x -- dot inference P
noncomputable def bleach (v:I→ℕ)(s:ℕ→ℂ): Ruby.Hue c N I := ⟨Y.bud,fun i=>s (v i) • Y.mean i⟩
noncomputable def weight (v:I→ℕ)(s:ℕ→ℂ): Gem c N I:=⟨X.addr,fun i=>s (v i) • X.view i⟩
lemma earns (x:Grid c)(i:I): letters (weight X v s) p.threshold x i=s (v i) • letters X p.threshold x i:=by
    unfold letters masked; dsimp only [weight,Set.indicator]; split; rfl; exact (smul_zero ..).symm
-- wax in bounded pack of frequencies; reuse olig `U` estimate.Quits
variable (hs:∀ i,‖s (v i)‖≤r) (hr:0≤r)
include hs hr
lemma payments (h:Licence p u T t X): Licence p u (r*T) t (weight X v s):=by
    obtain ⟨f,hf,hV⟩:=h.zone; refine ⟨fun i=> r*f i,fun i=> ?_,fun i=> ((Phased.complexTone (hV i) (s (v i))).stretches (Subset.refl _) (mul_le_mul_of_nonneg_right (hs _) (hV i).travel))⟩
    convert! budget_scale hr (hf i) using 1; ext j; change (if (X.addr j).site=i then _ else _) =_; split; exact mul_assoc ..; rw [mul_zero]
lemma bleachPay (h:Wax Y u p.B a T t): Wax (bleach Y v s) u p.B a (r*T) t:=by
    obtain ⟨f,hf,hV⟩:=h.expense; refine ⟨⟨fun i x y hv hz=> congr_arg (s (v i) • ·) (h.burns.bond i x y hv hz), fun i=>measurable_const.smul (h.burns.meas i),fun i V hx=>(h.burns.non i V (fun hz=>hx ?_)),fun i x=>?_⟩,(fun i=>r*f i),?_,fun i V=>?_⟩ -- Tall
    · exact (congr_arg (s (v i) • ·) hz).trans (smul_zero ..)
    · unfold Gated; rw [show (bleach ..).mean _ _= _ from (show (bleach Y v s).mean i x=s (v i) • _ from rfl),map_smul]; exact Subalgebra.smul_mem _ (h.burns.lives i x) _
    · intro i; convert! budget_scale hr (hf i) using 1; funext j; split
      next h0=> rw [if_pos (show i∈Y.bud j from h0)]; exact mul_assoc ..
      next hm=> rw [if_neg (show i∉Y.bud j from hm),mul_zero]
    rw [Ruby.tokenCC]; change ‖tokenC t (s (v i) • Y.mean i V)‖≤_; rw [map_smul,norm_smul]; exact mul_le_mul (hs _) (hV _ _) (norm_nonneg _) hr
omit hs hr
variable (b:ℕ→ℝ)
lemma realY (h:Yank Y v): Yank (bleach Y v fun i=>(b i:ℂ)) v:=by
    let P:= bleach Y v (fun i=>(b i:ℂ)); refine ⟨⟨fun i U k=> congr_arg Subtype.val ((swayC _ _ _).trans (congr_arg ((b (v i):ℂ) • ·) (Subtype.ext (h.gauge i U k)))) ,fun i U=>?_,fun i U=>AccentFit.mulC _ (h.fit i U) _⟩,fun s k g he=>?_⟩
    · change Regal c N ((b (v i):ℂ) • Y.mean i U)= (b (v i):ℂ) • _; rw [regC,h.real]; simp
    obtain ⟨e,h',hE,hP⟩:=h.glamour s k g he; refine ⟨e,h',hE,fun i U=>?_⟩; change Diode _ _ _ _ ((b (v i):ℂ) • Y.mean i (sky s U)) = (b (v (e i)):ℂ) • Y.mean (e i) U; rw [swayC,hE,hP]
lemma wax_post (h:Wax Y u p.B a T t)(hk:σ ≤ a)(hu:T≤ x): Wax Y u p.B σ x t:=by obtain ⟨f,hf,hV⟩:=h.expense; exact ⟨h.burns, f, fun i=>budget_loosen (Shells.Warmlet.fresh f _ hf hk (fun i=>(norm_nonneg _).trans (hV _ 1)) i) hu,hV⟩
lemma door (h:Yank Y v): Y.Doorways:= ⟨h.gauge,h.real,h.fit,fun s k g hW=>by obtain ⟨e,ht,-,hg⟩:=h.glamour s k g hW; exact ⟨e,ht,hg⟩⟩
end YM.QCD.Relight
#print axioms YM.QCD.Relight.bleachPay
