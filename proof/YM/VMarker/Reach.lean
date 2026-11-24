import YM.VMarker.Eclipse
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Twist
open QCD QCD.Grass QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Cupola Function Loom QCD.Cove
open MeasureTheory NormedSpace Filter
open Kites Ruby Finch Relight Plate Stew Stew.Phased Reggae
open scoped Topology BigOperators ContDiff Classical Matrix
variable {A B I E J K R U:Type}[Fintype I] {c:Side}{N:ℕ}
open Stitch
variable (P:Rise c N E K) (F:Reel c N I R)(G:Film c N I U)(O:Register P F G)
local notation "Z"=> Keys c N
local notation "Xq"=> Ribbon.Spine I
local notation "U★"=>rootR Xq (Keys c N)
local notation "P★"=>vacR Xq (Keys c N)
local notation "P₁"=> fun i=>rootR Xq Z ∘ P.main i
local notation "P₂"=> fun i=>rootR Xq Z ∘ P.plug i

local notation "Y★"=> result P F G O
variable {q:I→Bool}{p:I→Site c}{t s h a v u ε q0 w ξ η x:ℝ}{m:ℕ}{f:E→ℝ}{g:K→ℝ}
-- shared capacities; use given basis and startup extra ledgers. Use ALL support Boost estates.E.Shape
open Jets Jets.Touch Push.AbsoluteSums Ruby LanternK Tablet Footprint
lemma hitLower (H:A→Support c)(f:A→ℝ)(h:0≤f)(hc:∀ i,(H i).Nonempty)(hp:u-a=v)(hz:0≤a) (he:Ac.Hit H m f u x): Ac.Hit H m f v (Real.exp (-a)*x):= by
   intro i; refine budget_mono (budget_scale (Real.exp_nonneg (-a)) (he i)) ?_ ?_; exact (fun j=>ite_nonneg (mul_nonneg (h j) (Real.exp_nonneg _)) le_rfl)
   intro j; split; next hh=> rw [mul_left_comm (Real.exp _),←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (h j); apply Real.exp_monotone; have H:1≤(coverNumber m (H j):ℝ):= Nat.one_le_cast.mpr ((Animals.price_pos ..).2 (hc j)); nlinarith
   next hh=> rw [mul_zero]
open Dust
-- w/h tilt shared payment at ANY λ for those physical costs.
structure Payment (p' : Rise c N E K) (X:Tablet p' I) (w t η T :ℝ)(B:ℕ)(U U₀:ℝ):Prop where
  budget : ∃ (f:E→ℝ)(g:K→ℝ), Cents p' f g w t ∧ Fill p' f g η η T U U₀ B ∧ X.Coins f g w t
-- math.Jet.Hit→Anchored via choose.
lemma at_price (F:A→RegularAddress c)(f:A→ℝ)(h:0≤f)(he:Ac.Hit (fun i=>(F i).support) m f u a) : Anchored (fun i=>(F i).site) f (fun i=>coverNumber m (F i).support) u a:=by
   intro i; refine budget_mono (he i) ?_ ?_; exact fun i=>ite_nonneg (mul_nonneg (h i) (Real.exp_nonneg _)) le_rfl
   intro j; split; next hh=> dsimp only; rw [if_pos (show i∈_ from hh ▸ (F j).anchor)]
   next hh=> exact ite_nonneg (mul_nonneg (h _) (Real.exp_nonneg _)) le_rfl
lemma anchorReach (H:E→RegularAddress c)(e:R↪E)(k:R→ℝ)(hE:∀ i,H (e i)=F.addr i)(hk:0≤k)(he: Ac.Hit (fun i=>(F.addr i).support) m k u a) :Anchored (fun i=>(H i).site) (clean e k 0) (fun i=>coverNumber m (H i).support) u a:=by
    intro i; apply clean_budget e; exact fun j=>ite_nonneg (mul_nonneg (cleanNN e k hk j) (Real.exp_nonneg _)) le_rfl
    · intro j hj; change (if (H j).site=i then clean e k 0 _ *Real.exp _ else 0) ≠ 0 at hj; by_contra hz; apply hj; rw [other e _ _ _ hz]; simp
    convert (at_price F.addr k hk he i) using 1; simp only [Function.comp_def,hE,became]
lemma faresTax (H:K→ Cove.Hat c)(e:U↪K)(k:U→ℝ)(hE:∀ i,H (e i)=G.addr i)(hk:0≤k)(hv:0 ≤x) (he:Ac.Hit (fun i=>(G.addr i).place) m (Film.fares N G k (fun _=>1) x) u a): Ac.Hit (fun i=>(H i).place) m (fun i=>(clean e k 0 i)*x^(H i).inv.card) u a:=by
    intro i; apply clean_budget e
    · exact fun j=> ite_nonneg (mul_nonneg (mul_nonneg (cleanNN e k hk j) (pow_nonneg hv _)) (Real.exp_nonneg _)) le_rfl
    · intro j hj; change (if i∈(H j).place then clean e k 0 j * _ * Real.exp _ else 0)≠0 at hj; by_contra hz; apply hj; rw [other e _ _ _ hz]; simp
    convert he i using 1; funext i; simp only [comp_apply,became,hE,Film.fares,GasP.taxed,_root_.abs_one, prod_const_one,one_mul,mul_comm (k i)]
end YM.MassiveQCD.Twist
#print axioms YM.MassiveQCD.Twist.faresTax
