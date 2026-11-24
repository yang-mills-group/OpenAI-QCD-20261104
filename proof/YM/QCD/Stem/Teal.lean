import YM.QCD.Stem.Glo
/-! # Long habitat entrance. Ticks κ allocated before Price via mass roll.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove
variable {C:Side}{D D' w j:ℕ}{d r t t' p p' :ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove YM.Next.Scheduling Footprint Moss
section long
variable (x:Gem c N I)(z:I→ℝ)
lemma pardon (g g':I→ℕ) (ht:Anchored (fun i=> (x.addr i).site) z g t r)(hk:∀ i,g' i ≤ g i)(hp:0≤t)(hv:∀ i,0 ≤ z i): Anchored (fun i=> (x.addr i).site) z g' t r:=by
   intro u; apply budget_mono (ht u)
   · intro i; split; exact mul_nonneg (hv i) (Real.exp_pos _).le; exact le_rfl
   intro i; split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hk i)) hp)) (hv i); exact le_rfl
lemma onlyLong (W:I→Prop) (hw:∀ i,0≤ z i)(hp:Anchored (fun i=> (x.addr i).site) z (fun i=>coverNumber B.B (x.addr i).support) (t+1) r) (hz:∀ i,W i → d ≤ coverNumber B.B (x.addr i).support): Anchored (fun i=> (x.addr i).site) (fun i=>if W i then z i else 0) (fun i=> coverNumber B.B (x.addr i).support) t (Real.exp (-d)*r):=by
   intro u; apply budget_mono (budget_scale (Real.exp_pos _).le (hp u))
   · intro i; split_ifs <;> first | positivity [hw i] | rw [zero_mul]
   intro i; split
   next h=> dsimp only; split
            next he=> let v:ℝ:=coverNumber B.B (x.addr i).support; rw [mul_left_comm,←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (hw _); apply Real.exp_monotone; have ht:d≤ v:=hz i he; change t*v≤ -d+ (t+1)*v; linarith
            next he=> rw [zero_mul]; have hI:=hw i; positivity
   next h=> rw [mul_zero]
noncomputable def portage (P:BudgetPoint)(h:0<n):BudgetPoint:= { P with B:=n,B_pos:=h }
lemma earnsPort (hn:0<n)(h:n≤ B.B)(ht:0≤t)(hp:Licence (portage B hn) t r p x): Licence B t r p x:=by
   obtain ⟨f,hf,H⟩:=hp.zone; refine ⟨f,pardon x f _ _ hf (fun i=> ?_) ht (fun i=>(H i).travel),?_⟩
   · exact cover_earns h _
   intro i; have h:=H i; exact ⟨h.room,h.gated,h.use,h.pole,h.Borel,h.travel⟩
end long
section coat
variable {a u m :ℝ} (t:ℝ) (A:Silo c) (G:BankP c)(Q:St c) (ht: Run.Pack id id t u n Q d A G) (hv :0<t)
include ht hv
local notation "E"=> sealG A N
noncomputable def unkempt (n: Side) (w:ℕ)(A: Silo n)(N:ℕ): Gem n N (Tick n):= muteK (sealG A N) (fun i=> i∉kiln n w)
lemma viableK (i:Tick c)(hi:¬ fertile i): (E).view i=0:=by
   have he (i':Tick c) (he:¬ fertile i') U: pairQ A i' U=0:=by unfold pairQ; rw [debtless ht i' U he hv]; exact map_zero (blockL _ _)
   funext U; unfold sealG; change paleF N (gleam A U i)=0; unfold gleam; rw [he i hi,he _ (mt (fertileD i).2 hi),add_zero,smul_zero,noneC]
omit ht hv
abbrev meterQ (n w:ℕ):ℝ:= ((w:ℝ)-2*n)/(4*n+2)
lemma attrition (i:Tick c)(hv:fertile i)(h:i∉kiln c w)(n:ℕ):meterQ n w ≤ coverNumber n (dispatch i).support:=by
   have he:∃ u∈i.2.2, w< separation i.1 u:=by
     by_contra hh; apply h; push Not at hh; exact mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,fun p hp=> (tendle ..).2 (hh p hp)⟩⟩ -- type
   obtain ⟨u,hp,hU⟩:=he; have hd:= lt_of_lt_of_le hU (Corona.extent i.2.2 n hv.1 hp); rw [show (dispatch i).support= i.2.2 from if_pos hv]; apply (div_le_iff₀ (by positivity : 0<(4*n+2:ℝ))).mpr; have hf: (w:ℝ) < coverNumber n i.2.2*((4:ℝ)*n+2)+2*n:=by exact_mod_cast hd
   linarith
include ht hv
lemma notables (hn:0<n)(hq:n ≤ B.B)(hr:0≤r)(he:Licence (portage B hn) (r+1) m p E):Licence B r (Real.exp (-(meterQ n w))*m) p (unkempt c w A N):=by
   let X k:= k∉kiln c w ∧ fertile k
   apply earnsPort (unkempt c w A N) hn hq hr
   obtain ⟨z,hz,hy⟩:= he.zone; let f i:= if X i then z i else 0; have he : Anchored (fun i=> ((E).addr i).site) f (fun i=>coverNumber n ((E).addr i).support) r (Real.exp (-(meterQ n w))*m):=by convert! onlyLong E z (B:=portage B hn) X (fun i=> (hy i).travel) hz (fun i h=> attrition i h.2 h.1 n) using 1; funext i; unfold f; split_ifs<;> rfl
   refine ⟨f,he,?_⟩; intro i; unfold unkempt; rw [eitherX]; dsimp only [f,X]
   split
   next hh => by_cases hy': fertile i; · rw [if_pos (And.intro hh hy')]; exact hy _
              rw [if_neg (show ¬ (i∉kiln c w ∧ fertile i) from fun h=> hy' h.2),viableK _ _ _ _ ht hv i hy']; exact freeK ..
   next hh=> simp only [hh,not_true,false_and,if_false]; exact freeK ..
end coat
end YM.QCD.Stem
