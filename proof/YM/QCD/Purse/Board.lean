import YM.QCD.Purse.Table
import YM.QCD.Tax.Glory
/-! # Real layer. hue dictionaries on arbitrary virtual-τ labels; convert only via corresponding j Tape. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
open Garden Stew Dust Brick YM.Next.Free Jets.Touch Orbit Further Leaf Tee Flume Quarry Pine
open Planned.AtomRegular
open Run Jets Jets.Sun
open Ac Trees Labels Animals Further.ShellBirth49.Fusing Collide
open Trees Ac Further.ShellBirth49.Fusing Collide
open Labels
variable {p i j' m m':ℕ}
-- Anchor dictionary only needs single B. Y estimator equality of register. 
variable {E J: Type}[Countable E][Countable J]{D:Type}[Fintype D]
variable (H) (P': Send S.ratio N D) (Y':Rise f N E J)
local notation "L₀"=> P'
set_option quotPrecheck false
local notation "K₀"=> Wound (roof P' Y' 30 (radiusB s))
local notation "ζ"=> radiusB s
local notation "Y!"=> deckHue H P' Y' (roof P' Y' 30 ζ)
local notation "Z!"=> united (Y!) Y
local notation "A⁔"=> Warmlet H Y P' Y'
namespace Warmlet
local notation "Tz"=> (lore (trimP T R δ β B₀))
variable (p : Warmlet H Y P' Y')
variable (V:Cash W s μ L Q o C T (lore (trimP T R δ β B₀)))
def frostQ (m:ℕ):ℕ:= (((m+1)+1)+((m+1)+1)+1)^4
lemma brew (p:Warmlet H Y P' Y') (h:¬Small H Y P' Y' p V)(hz:0 < ζ): ((radiusB s):ℝ) ≤ (coverNumber ζ (past H Y P' Y' p):ℝ)* frostQ Q.halo:=by
   have ht:= Corona.cover_mono (stretchP H Y P' Y' p) ζ; have hp : ζ ≤ coverNumber ζ (perch H Y P' Y' V p).support:=(lt_of_not_ge h).le; rw [ (plateK H Y P' Y' V p).1] at hp
   exact_mod_cast (show ζ ≤ coverNumber ζ (past H Y P' Y' p)*frostQ Q.halo from (hp.trans ht).trans (touring _ Q.halo _ ζ hz le_rfl))
noncomputable def chill (m:ℕ)(x:ℝ):= Real.exp (-(frostQ m:ℝ)⁻¹ * radiusB x)
lemma frosty (L:Side)(m:ℕ) (A C:ℝ)(ha:0<A):∀ᶠ x in atTop,chill m x*King.flowM L x ≤ A*chip L x:=by
   let t:=(frostQ m:ℝ)⁻¹; have ht:0 < t:=by unfold t frostQ; positivity
   have hh: Rate su L (-3) (chill m):= ((Rate.cutoff ht).compare (Eventually.of_forall fun x=>?_)); swap
   · unfold chill; change _ ≤|Real.exp (-t*Stores.till x)|; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; exact mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (Nat.div_le_self (radiusB x) _)) (by change -t ≤ 0; linarith)
   have h:= (hh.mul (show Rate su L (-(3/10)) (King.flowM L) from Rate.power)).mul (top_chip L)
   filter_upwards [h.below (by norm_num) A ha,Delay.shift_pos su L] with x hx hX; have hv:= (le_abs_self _).trans hx; rw [← div_eq_mul_inv] at hv; exact (div_le_iff₀ (healthy_chip hX)).mp hv
variable {g:Clusters (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y).Bright→ℝ} {p q' v' x:ℝ}
local notation "o!"=> trunkP H Y P' Y' V
local notation "t!"=> Small H Y P' Y'
-- generic
lemma walk (f:ι→Prop)(A:(i:{x:ι//f x})→ℝ) (x:ι→ℝ)(hx:∀ i,¬f i→x i=0)(he:∀ (i:{x:ι//f x}),x i.val=A i)(hQ:SumBudget A p): SumBudget x p:=by
   apply budget_of_sum
   · intro i; by_cases hf:f i; · exact (he ⟨i,hf⟩).symm ▸ hQ.1 ⟨i,hf⟩
     exact (hx _ hf).ge
   intro s; let t:= s.filter f; rw [← sum_subset (filter_subset f s) (f:=x) ?_]; rotate_left
   · intro i hi hy; exact hx i (fun h=>hy (mem_filter.mpr ⟨hi,h⟩))
   let V:t→{x//f x}:=fun i=>⟨i.val,(mem_filter.mp i.property).2⟩; have hV:Function.Injective V:=fun _ _ hh=> Subtype.ext (congr_arg (fun i : {i// f i} => i.val) hh); have hp:=budget_pull V hV hQ
   change ∑ i∈t,x i ≤_; rw [← sum_attach t x]; apply le_trans _ (budget_sum hp t.attach); exact sum_le_sum fun i _=> (he (V i)).le
lemma answer {P':ι→ℝ}{O:ι→Site c}{Y₁:ι→ℕ}(J:ι→Prop)(U:{x//J x}→ℝ) (hU:Anchored (fun i:{x//J x}=> O i.val) U (fun i=> Y₁ i.val) A C) (he:∀ i,¬J i→P' i=0) (hp:∀ i:{x//J x},P' i=U i): Anchored O P' Y₁ A C :=by
    intro i; apply walk J (fun j:{x//J x}=> if O j.val=i then U j * Real.exp (A*Y₁ j.val) else 0) _ _ _ (hU i)
    · intro j hj; simp only [he j hj,zero_mul,ite_self]
    intro j; rw [hp]
lemma gloomy (hh :Ac.Hit (seatP (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y).lightF) (radiusB s) g (a+1) p)(hx:0<ζ)(h:0≤g):
    Anchored (fun i:A⁔=> ((o!) i).site) (fun i=>if Small H Y P' Y' i V then 0 else g (individual i.code)) (fun i=>coverNumber ζ ((o!) i).support) a (chill Q.halo s*p):=by
    let d:A⁔→Clusters (Z!).Bright:= fun i=>individual i.code; have hp:Function.Injective d:=copyQ H Y P' Y' -- not exactly
    let z:=chill Q.halo s; have ht:0 ≤ z:=(Real.exp_pos _).le; intro x
    refine budget_mono (budget_scale ht (budget_pull d hp (hh x))) (fun i=> ?_) ?_
    · split; swap; exact le_rfl
      exact mul_nonneg (by dsimp only; exact ite_nonneg le_rfl (h _)) (Real.exp_pos _).le
    intro i; split
    next he=>
      by_cases hv:Small H Y P' Y' i V; · dsimp only; rw [if_pos hv, zero_mul]; exact (budget_scale ht (budget_pull d hp (hh x))).1 i
      let n:=coverNumber ζ ((o!) i).support -- notation dot
      have hU : seatP (Z!).lightF (d i)=((o!) i).support:=((cottage _ _ _ i.earns).1).trans (by rw [trunkP,if_neg hv]; rfl)
      have hR : x∈seatP (Z!).lightF (d i):= hU.symm ▸ he ▸ ((o!) i).anchor -- try
      dsimp only; rw [if_neg hv,hU,if_pos (hU ▸ hR)]
      rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (h _); unfold chill; rw [← Real.exp_add]; apply Real.exp_monotone
      let B:ℝ:= frostQ Q.halo; have hB:0<B:=by unfold B frostQ; positivity
      have hz : ((radiusB s):ℝ) / B ≤ (n:ℝ):=(div_le_iff₀ hB).mpr (by unfold n; rw [trunkP,if_neg hv]; exact brew _ _ _ _ V i hv hx)
      change a*(n:ℝ) ≤ -(B⁻¹)*_+ (a+1)*_; rw [div_eq_mul_inv] at hz; linarith only [hz]
    next _=> exact (budget_scale ht (budget_pull d hp (hh x))).1 i
variable (β':E→ℝ)(G: Hera.Rights su j)
-- small princely payroll
noncomputable def petty (N':Libretto su j)(Z:Hera.Rights su j)(O:BudgetPoint)(ψ:ℝ)(β':E→ℝ) (p: Warmlet H Y P' Y'):=if Small H Y P' Y' p V then (if h: Warmlet.prince H Y P' Y' p then doll H Y P' Y' O N' Z ψ β' ⟨p,h⟩ else 0) else 0
lemma perky (hp: Anchored (fun i:Duke H Y P' Y'=> (perch H Y P' Y' V i.val).site) (doll H Y P' Y' O N' G p β') (fun i=> coverNumber ζ (perch H Y P' Y' V i.val).support) a u):
    Anchored (fun i:A⁔=> ((o!) i).site) (petty H Y P' Y' V N' G O p β') (fun i=>coverNumber ζ ((o!) i).support) a u:=by
    let f i:=petty H Y P' Y' V N' G O p β' i
    apply answer (P':=f) (prince H Y P' Y') (fun i:(Duke H Y P' Y')=> f i.val) ?_ (fun i hv=> by simp [f,petty,hv]) (fun _=>rfl)
    intro x; refine budget_mono (hp x) ?_ ?_
    · intro i; unfold f petty trunkP; simp only [dif_pos i.property]; split -- inspect
      next h=> exact (hp x).1 i
      next h=> simp
    intro i; unfold f petty trunkP; simp only [dif_pos i.property]; split; exact le_rfl; simp only [zero_mul,ite_self]; exact (hp x).1 i
-- for many card≥2; charge even if no Σ.E acts ok.
variable {t₀:Fj D E J→ℝ}
noncomputable def wageP (V:Cash W s μ L Q o C T (lore (trimP T R δ β B₀))) (p q:ℝ)(w:Fj D E J→ℝ)(i:Warmlet H Y P' Y'):= if Small H Y P' Y' i V∧2≤ i.label.val.card then p⁻¹*(∏ i∈i.label.val,w i) * (q*((ops i.label.val).card+1:ℝ)) else 0
lemma wageG (hv: Ready (roof P' Y' Q.halo ζ) ζ t₀ a u 1 r)(he:2*r<1)(hx:0 < p)(hz:0≤q)(ha:0≤a): Anchored (fun i:A⁔=> ((o!) i).site) (wageP H Y P' Y' V p q t₀) (fun i=>coverNumber ζ ((o!) i).support) a ((q*p⁻¹)*(2*u*(2*r)^1*(1-2*r)⁻¹)):=by
    intro x; let R i:= roof P' Y' Q.halo ζ i; let d:A⁔ → Finset (Fj D E J):= fun i=> i.label.val; let A (i: Finset (Fj D E J)):= i.biUnion R
    have hI : Function.Injective d:=iden H Y P' Y'; have hh:=budget_pull d hI (bold hv he ha hx hz (sky P' Y') A x (fun _=>Subset.refl _)); refine budget_mono hh ?_ ?_
    · intro i
      apply ite_nonneg _ le_rfl
      apply mul_nonneg _ (Real.exp_pos _).le
      unfold wageP; apply ite_nonneg _ le_rfl
      have hm:0 ≤ ∏ j∈ i.label.val,t₀ j :=prod_nonneg (fun i _=>hv.2.2.2.2.1 i); positivity
    intro i; by_cases he':Small H Y P' Y' i V∧2≤ i.label.val.card; swap
    · rw [wageP,if_neg he']; simp only [zero_mul,ite_self]; exact hh.1 _
    have ht : ((o!) i).support = A (d i):= by rw [trunkP,if_pos he'.1]; exact (plateK H Y P' Y' V i).1
    split
    next hz=>
       have he : x ∈ A (d i):=ht ▸ hz ▸ ((o!) i).anchor -- substitution?
       rw [wageP,if_pos he',if_pos (And.intro he'.2 (And.intro he i.label.property))]; dsimp only; rw [ht]; exact le_rfl
    next h=> exact hh.1 _
end Warmlet
end YM.QCD.Shells
