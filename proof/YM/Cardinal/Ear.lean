import YM.Cardinal.Faults
/-! # Singleton report tape, parity generalized. With mask bill requiring on-mask sizes only. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t t₁ t₂:ℝ}{O: BudgetPoint}
namespace Card
namespace Iris
variable {q:Bool} (N)(o:Site c)
local notation "M"=> Ribbon.ample N Unit
local notation "T"=> topM
local notation "Vk"=> goldM q
local notation "K"=> Keys c N
local notation "R"=> Spine Iris.alpha
local notation "B!"=>Patio (Keys c N ⊕ Spine Unit)
local notation "p!"=>pluck K (goldM q)
set_option quotPrecheck false
open QCD.Stew
-- Singleton Report coefficients. products of markers vanish. Film.Linearity pack free.C
open NormedSpace
variable (F: Patron.Rail c N E)(Y:Film c N Unit J)(S:Support c)
variable (V:Grid c)
noncomputable local instance : Fintype (Cove.Hat c):=Fintype.ofFinite _
local notation "N'"=> banknote N (fun _:Unit=>o) v
local notation "E⁺"=>rootR R K
local notation "e₀"=> E⁺ (Kites.heartK F t V)
local notation "W₀"=> Wcall N F Y V (t:=t)
variable (D:Grid c→ EvenA c N)
variable {τ g lM :ℝ}
lemma sink_add (X:Film c N Unit U) (h:Y.Stock N O.B τ a v A (fun _=>1))(hp:X.Stock N O.B τ a v g (fun _=>1)): (addFilm N Y X).Stock N O.B τ a v (A+g) (fun _=>1):=by
    obtain ⟨f,hf,h⟩:= h.price; obtain ⟨p,hp,h'⟩:=hp.price; let F:=addFilm N Y X; let W:= Sum.elim f p
    refine ⟨W,fun i=>?_,fun i=>?_⟩
    · rcases i with i|i; exact hf i; exact hp i
    exact Extra.Iteration.Cost.sum (h i) (h' i)
lemma sink_by (h:Y.Stock N O.B τ a v A (fun _=>1))(u:ℂ): (feeK N Y u).Stock N O.B τ a v (‖u‖*A) (fun _=>1):=by
    obtain ⟨f,hf,h⟩:= h.price; refine ⟨fun j=>‖u‖*f j,fun i V=>?_,fun i=>?_⟩
    · unfold Film.glyph; rw [show light (Keys c N⊕Spine alpha) ((feeK N Y u).mark i V)= u • light _ (Y.mark i V) from map_smul (light (Keys c N⊕Spine alpha)) ..,load_scale]; exact mul_le_mul_of_nonneg_left (hf ..) (norm_nonneg _)
    convert! budget_scale (norm_nonneg u) (h i) using 1; funext j; split
    next he=> rw [if_pos (show _ from (show i∈ (Y.addr j).place from he))]; unfold Film.fares taxed; simp only [feeK]; ring
    next he=> rw [if_neg (show _ from (show i∉ (Y.addr j).place from he)),mul_zero]
-- Punch anchored.Hit.Atoms.Selection
lemma hit_collect (S:J→Support c)(b:J→ℝ)(hp:∀ i,o∈S i)(he: Ac.Hit S k b a v) : SumBudget (fun i=> b i*Real.exp (a*coverNumber k (S i))) v:= by simpa only [hp,↓reduceIte] using he o
lemma spend_collect (S:J→ Support c)(b:J→ℝ)(hv: SumBudget (fun i=> b i*Real.exp (a*coverNumber k (S i))) v) : Ac.Hit S k b a v:=by intro i; exact budget_mono hv (fun j=> by split; exact hv.1 j; exact le_rfl) fun j=>by split; rfl; exact hv.1 j
lemma tax_charge (f:J→ℝ)(u:ℝ)(j:J) : Film.fares N Y f (fun _=>1) u j= u^(Y.addr j).inv.card*f j:= by unfold Film.fares taxed; simp only [abs_one,prod_const_one,one_mul]
lemma rigid_mark (h:Y.Beat N (fun _:Unit=>o) (fun _=>q) t)(i:J) : o∈(Y.addr i).place:=by obtain ⟨j,hj⟩:=h.commits i; exact h.spark i (mem_image_of_mem _ hj)
lemma shrink (h:Y.Stock N O.B τ a v A (fun _=>1))(hh: g ≤ a)(ht:A ≤ C)(hz:τ≥w)(hx:0 ≤ w) : Y.Stock N O.B w g v C (fun _=>1):=by
    obtain ⟨f,hf,h⟩:= h.price; have hs(i):0 ≤ f i:= (show 0 ≤ Film.glyph N Y 1 i v from norm_nonneg _).trans (hf ..); refine ⟨f,hf,fun i=>budget_mono (budget_loosen (h i) ht) (fun j=>?_) fun j=>?_⟩
    · split; rw [tax_charge N Y]; positivity [hs j]; exact le_rfl
    split; next hi=> rw [tax_charge,tax_charge]; have hg:hx=hx:=rfl; have hη: 0 ≤ τ:=hx.trans hz; have hζ:=hs j; gcongr
    next hh=> exact le_rfl
lemma loaded {I:Type}[Fintype I](x:Alg I)(w:I→ℝ)(he:∀ i, 1≤w i) [DecidableEq I]: ‖x‖ ≤ load w x:=by
   rw [dry w (fun i=> zero_lt_one.trans_le (he i)), Grass.norm_def]; apply sum_le_sum; intro i _; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_prod (fun j _=>he j)) -- `dec` mismatch norm_def.
lemma absentD (h:Y.Stock N O.B τ a v A (fun _=>1))(hx:Y.Beat N (fun _=>o) (fun _=>q) t)(hp:1 ≤ τ)(hr:1≤v)(hi:0≤a): Summable fun i=>‖Y.mark i V‖:=by
    obtain ⟨f,hf,h⟩:= h.price; let g i:=Film.fares N Y f (fun _=>1) τ i; have hp':SumBudget (fun i=>g i*Real.exp (a*coverNumber O.B (Y.addr i).place)) A:=hit_collect o _ _ (rigid_mark N o Y hx) h -- sig
    refine hp'.2.1.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> (?_ : ‖Y.mark i V‖≤_))
    calc
       _ ≤ Film.glyph N Y V i v:= loaded (Y.mark i V).val _ (fun j=> by rcases j with j|j; exact hr; exact le_rfl)
       _ ≤ f i:= hf ..
       _ ≤ _:= by
          change _≤ Film.fares _ _ _ _ _ _*_; have hz:0≤ f i:= (show 0≤Film.glyph N Y V i v from norm_nonneg _).trans (hf ..); rw [tax_charge]; exact (le_mul_of_one_le_left hz (one_le_pow₀ hp)).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (mul_nonneg hi (Nat.cast_nonneg _)))) -- implicit i needed
variable (X:Puff c N J q)
open Puff
-- stool plus Mint.Abstaining. Step at λ opportunities. Marker intensity.
lemma grow_shape (i: Grid c) (hp:∃ g:J→ℝ,(∀ j,Sight (X.addr j).support o k O v (X.fill j) (g j)) ∧ Ac.Hit (fun j=>(X.addr j).support) O.B g a A)(ht:0≤a)(hs:1 ≤v)(hv:Seal N o X) : Summable (fun j=> Reel.mist (roll N X) O.threshold j i):=by
    obtain ⟨g,hp,hQ⟩:=hp; let f(N:ℝ) i:= g i*Real.exp N
    have hl:= hit_collect o _ _ (fun j=> (show o∈(X.addr j).support from (hv.anchor j) ▸ (X.addr j).anchor)) hQ; have hV:=zero_lt_one.trans_le hs
    apply Summable.of_norm; refine hl.2.1.of_nonneg_of_le (fun _=> norm_nonneg _) (fun j=>?_)
    by_cases he:Healthy O.threshold (X.addr j).support i; swap; · rw [Reel.mist,masked_ne _ _ _ _ (show ¬Healthy _ ((roll N X).addr j).support i from he),norm_zero]; exact hl.1 j
    rw [Reel.mist,masked_eq _ _ _ _ (show Healthy _ ((roll N X).addr j).support i from he)]
    let z:= (roll N X).mark j i
    have hW: ‖z‖≤load (fun _=>v) (X.fill j i):= (loaded z.val (Stitch.Tablet.chip v K R) (fun j=> by rcases j with j|j; exact hs; exact le_rfl)).trans_eq ((Stitch.Tablet.polite_bill T z (worthE _ _ _ (X.beams j) i) hV).trans (congr_arg (fun x:Lat.Fields c N=> load (fun _=>v) x) (worthG N _ _ (X.beams j) i))) -- Eq orientation and signature
    exact (hW.trans ((viewer o _ k hV).trans ((hp j).pole i he [] (Nat.zero_le _) (fun j h=>by simp at h)))).trans (le_mul_of_one_le_right (hp j).travels (Real.one_le_exp (mul_nonneg ht (Nat.cast_nonneg _))))
end Iris
end Card
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Card.Iris.grow_shape
