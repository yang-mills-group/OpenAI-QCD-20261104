import YM.Cardinal.Girdle
/-! # Lighthouse over charged coordinates.Both ways.Plane. Step and root extraction algebra.-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {a b t θ v:ℝ}{k d n j:ℕ}{c:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets
open MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local QCD.Kit
namespace Girdle
local notation "X"=> Grid c→Lat.Fields c 6
local notation "K"=> Keys c 6
variable (P:BudgetPoint) (q:Bool)(V:Grid c)(Y:Support c) (F G:Grid c→Lat.Fields c 6)
variable {o:Site c}
variable (ht: Flame F P Y o t d j a) -- o undecl
variable (s:ℂ)
include ht
lemma flare_add (h:Flame G P Y o t d j b)(hv:0≤t): Flame (F+G) P Y o t d j (a+b):=by
    refine ⟨Terrain.persuaded ht.sight h.sight hv,fun i hi=> ?_⟩
    let u:= (framesF (purseX o d t)).comp (mantel (A:=K) i); refine ⟨add_nonneg ht.sight.travels h.sight.travels,fun V hV l hl hQ=>?_⟩
    let x:=u∘F; let y:=u∘G; change ‖leftDerivs (u∘(F+G)) l V‖≤ _; rw [show u∘(F+G)=x+y from funext fun i=>map_add u ..,left_add l (u.contDiff.contDiffAt.comp (f:=F∘increment V) _ (ht.sight.use V hV)) (u.contDiff.contDiffAt.comp (f:=G∘increment V) _ (h.sight.use V hV)) hl]; exact (norm_add_le ..).trans (add_le_add ((ht.issues i hi).2 V hV l hl hQ) ((h.issues i hi).2 V hV l hl hQ))
lemma flare_by : Flame (s • F) P Y o t d j (‖s‖*a):=by
    refine ⟨Terrain.scaledL ht.sight s,fun i hi=>⟨mul_nonneg (norm_nonneg _) ht.sight.travels,fun V hV l hl hQ=>?_⟩⟩
    let v:= framesF (purseX o d t); let M:= (v.comp (mantel i)); let L:= ((s • (ContinuousLinearMap.id ℂ (Alg K))).restrictScalars ℝ); have hx:M∘(s • F)= L∘ (M∘F):=by
       funext i; change changeVars _ (panel _ (s • F i))= s • changeVars _ (panel _ _); rw [map_smul,map_smul] -- changeVars goals
    change ‖leftDerivs (M∘(s • F)) l V‖ ≤ _; rw [hx,left_linear L l (M.contDiff.contDiffAt.comp (f:=F∘increment V) _ (ht.sight.use V hV)) hl]; change ‖s • (leftDerivs (M∘ F) l V)‖≤_; rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((ht.issues i hi).2 _ hV _ hl hQ) (norm_nonneg _)
omit ht
lemma flare_zero : Flame (0:X) P Y o t d j 0:=by
    refine ⟨Terrain.zeroL,fun i hi=>⟨le_rfl,fun V hV l hl hQ=>?_⟩⟩; have h':framesF (A:=K) (purseX o d t) ∘(mantel i∘ (0:X))=0:= funext fun j=> by
         change framesF _ (mantel i 0)=0; rw [map_zero,map_zero]
    rw [h']; rw [show leftDerivs (0:X) l V=0 from ?_,norm_zero]; simpa only [ite_self] using! Work.G07.left_const (0:Alg K) l V
end Girdle
namespace Orientation
variable (H:TaperHol){U:Hol su}(A:Exhibit U) (B₀ : Basis (Fog d) ℂ (Label d)) (b:Cover)(d) -- U undecl
local notation "Θ" => Grid c→Lat.Fields c 6
local notation "K"=> Keys c 6
variable (F:Grid c→ Lat.Fields c 6)(q:Bool)
abbrev graphs (X:Label d): Grid c→ Lat.Fields c 6:= (Realize.placed (A.t d) c b (A.lead d X))
lemma placed (x:Label d)(V:Grid c): graphs d A b x V=dart (A.F d) (A.U d) (A.t d) c b V x.val:=by
    change places b (A.lead d x) V=_; unfold Cylinder.places; simp_rw [← porch_eval,A.label]; exact dart_ship ..
lemma graphite (x:Label d)(u:Lat.Frame c)(V:Grid c): slots 6 u (graphs d A b x (Lattice.gauge u V))=graphs d A b x V:=by rw [placed,placed,wind_gauge,((label_law _).1 x.property).2]
lemma graphing (x:Label d)(q:Bool)(he:moored x.val q): moon 6 (graphs (c:=c) d A b x) q:=by
    intro V; let f:= dart (A.F d) (A.U d) (A.t d) c b V; have h: Grass.grade (graphs d A b x V)= gammaQ q • graphs d A b x V:=by rw [placed,foldG,he,map_smul]
    cases q; · exact (h.trans (one_smul ..))
    exact (h.trans (neg_one_smul ..))
lemma graph_obs (x:Label d)(h:Merian.SmallT c (A.t d) n): ActionTest H b (graphs (c:=c) d A b x) x.val :=Merian.riseT H U b A x h
variable {d}
local notation "N"=> Pairs (SpinMode d)
lemma acting (d:ℕ)(G: Θ)(x:Pol d)(hp: ActionTest H b G x) (s:ℂ) : ActionTest H b (s • G) (s • x):=by
    intro J; have he:= hp J; have h1 : moment (d:=d) H b J (s • G)= s • moment H b J G:=funext fun i=> by simp only [Beacon.moment, Pi.smul_apply,map_smul]
    have h2 : desired (s • x) J=s • desired x J:= funext fun i=> by rw [Pi.smul_apply,← observe,← observe,map_smul] -- observation definitional?
    have hz(f g:ℝ→SpinPol d)(h:Agrees f g): Agrees (s • f) (s • g):=by
          let A:= (s • (ContinuousLinearMap.id ℂ (SpinPol d))).restrictScalars ℝ; refine ⟨A.contDiff.contDiffAt.comp (f:=f) _ h.1,A.contDiff.contDiffAt.comp (f:=g) _ h.2.1,fun i hi=>?_⟩; change iteratedDeriv i (A∘f) 0=iteratedDeriv i (A∘g) 0; rw [clm_step _ _ _ (h.1.of_le ?_),clm_step _ _ _ (h.2.1.of_le ?_),h.2.2 i hi] <;> exact_mod_cast hi
    rw [h1,h2]; exact hz _ _ he
lemma actsPlus (d:ℕ)(G V:Θ)(x y:Pol d)(h0:ActionTest H b G x)(h1:ActionTest H b V y): ActionTest H b (G+V) (x+y):=by
   intro J; rw [show moment (d:=d) H b J (G+V)= moment H b J G + moment H b J V from funext fun i=>map_add (adapter ..) .., show desired (x+y) J= desired x J+desired y J from funext fun i=> by rw [Pi.add_apply,← observe,← observe,← observe,map_add]]; exact agreePlus (h0 J) (h1 J)
 where
    agreePlus {f g p q : ℝ→SpinPol d}(h:SourceRead.Agrees f g)(hx:SourceRead.Agrees p q):SourceRead.Agrees (f+p) (g+q) :=
     ⟨h.1.add hx.1,h.2.1.add hx.2.1,fun i hi=>by rw [iteratedDeriv_add (h.1.of_le ?_) (hx.1.of_le ?_), iteratedDeriv_add (h.2.1.of_le ?_) (hx.2.1.of_le ?_), h.2.2 i hi,hx.2.2 i hi] <;> exact_mod_cast hi⟩
lemma actsWear (d:ℕ)(G:Θ)(x:Label d)(t:ℝ)(hp:ActionTest H b G x.val) : ActionTest H b (engine t K∘ G) (dimming 1 t d x).val:=by
    intro J; have ht:=hp J; let S:=(engine t (Pairs (SpinMode d))).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; have hx : desired (dimming 1 t d x).val J=S∘ desired x.val J:=by
       funext i; rw [← observe]; change _= S (desired ..); rw [← observe]; change observation _ J i (Sieve.widths _ _ _)=S _; rw [countingG,one_smul]; rfl
    have hh: moment (d:=d) H b J (engine t K ∘ G)= S ∘ moment H b J G :=by
       -- rectangle. Exterior layer. commute rescalings
       funext i; let p:=glow (c:=c) (d:=d) H.T b i; let L:Matrix (Modes c 6) (SpinMode d) ℂ:=p; let P:=Matrix.fromBlocks L 0 0 L; change changeVars P (engine t K _)=engine t _ (changeVars P _)
       rw [← AlgHom.comp_apply,← AlgHom.comp_apply,engine,engine,←change_mul,←change_mul]; congr 2; ext i j; simp [Matrix.diagonal_mul,Matrix.mul_diagonal]; ring
    rw [hx,hh]; refine ⟨S.contDiff.contDiffAt.comp _ ht.1, S.contDiff.contDiffAt.comp _ ht.2.1,fun i hi=>?_⟩; rw [clm_step _ _ _ (ht.1.of_le ?_), clm_step _ _ _ (ht.2.1.of_le ?_),ht.2.2 i hi] <;> exact_mod_cast hi
lemma stylish (u:Label d) (p:PowerPair d): parityAct u.val=Sieve.widths 1 (-1) u.val:=by
   suffices h:parityAct (d:=d)= Sieve.widths 1 (-1) from congr_fun (congr_arg DFunLike.coe h) _
   apply (zBasis d).ext; intro i; rw [minted,widths_m]; unfold parityAct gen; rw [TensorProduct.map_tmul]; change _⊗ₜ[ℂ]Grass.grade _=_; rw [Grass.grade_mono,tmul_smul]; simp
lemma actor (x:Label d)(hp: ActionTest H b F x.val)(ht: moon 6 F q): moored x.val q:=by
    let F':= engine (-1) K ∘ F; have hg:F'= gammaQ q • F:=by
       funext i; have he: F' i=Grass.grade (F i):=by
          have hp:engine (-1) K= Grass.grade (A:=K):=by
             apply Grass.ext_atoms; intro i; unfold engine; rw [Grass.grade_atom,change_atom]; simp only [Matrix.diagonal_apply, ite_smul,zero_smul,Fintype.sum_ite_eq,Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul]
          exact DFunLike.congr_fun hp _
       rw [he,Pi.smul_apply]; cases q; · exact (show Plus _ from ht i) |>.trans (one_smul ..).symm -- syntax
       exact (show Minus _ from ht i) |>.trans (neg_one_smul ..).symm
    have he:= chooses H b ((label_law _).1 (dimming 1 (-1) d x).property).1 (Submodule.smul_mem _ _ ((label_law _).1 x.property).1) (actsWear H b d F x (-1) hp) (hg.symm ▸ acting H b d F x.val hp _); -- syntax
    exact (stylish x (0,∅)).trans he
end Orientation
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Orientation.actor
