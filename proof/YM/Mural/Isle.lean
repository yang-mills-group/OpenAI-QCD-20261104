import YM.VMarker.Spare
import YM.Mural.Army
import YM.Mural.Fil
/-! # Freezing a marked horoscope. Preserve assembly on harvested reel. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plette
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace
open Plate Stitch Tablet Ribbon Lattice Wilson Lat RG Twist PaletteT
open scoped BigOperators Topology Classical ContDiff
variable {I D E X ElType:Type} [Fintype I] {c:Side}{N:ℕ}
variable (p:Unit→Site c) (q:Unit→Bool) (Y:Reel c N Unit D)(F:Film c N Unit E)(Γ: Option I→D→Grid c→Patio (Keys c N⊕Spine Unit))(Φ:Option I→ E→Grid c→Patio (Keys c N ⊕Spine Unit))(P:Rise c N X ElType)
-- stands
noncomputable def script (i:Option I): Reel c N Unit D:= {Y with mark:= Γ i}
noncomputable def verse (i:Option I): Film c N Unit E:= {F with mark:= Φ i}
variable (W:Support c)(t:ℝ)
variable (G: Lat.Frame c)(K:Delta I)
local notation "S" i=> script Y Γ i
local notation "Q" i=> verse F Φ i
local notation "Λ"=> dance Unit G N
-- E color and blank assertions on mist only; startup actual E not outside healthy
structure JointE (Γ:Option I→ D→Grid c→ Patio (Keys c N⊕Spine Unit)):Prop where
   blocking i: Pillars (script Y Γ i) p q W
   neutral i V: Reel.mist (script Y Γ none) t i V=0
   sense i V: Binds K (dance Unit G N) (fun j=> Reel.mist (script Y Γ j) t i (gauge G V)) (fun j=> Reel.mist (script Y Γ j) t i V)
structure JointK :Prop where
   blocking i:Frails (verse F Φ i) p q t W
   unit i V: Φ none i V=0
   sense i V: Binds K (dance Unit G N) (fun j=> Φ j i (gauge G V)) (fun j=>Φ j i V)
variable (R: Twist.Register P Y F)
noncomputable def crew (i:Option I): Twist.Register P (script Y Γ i) (verse F Φ i):=⟨R.ear,R.tag,R.homeP,R.mark,R.freeP,R.freeG⟩
noncomputable abbrev bundle (i:Option I):Tablet P Unit:= result _ _ _ (crew Y F Γ Φ P R i) -- binder order
local notation "Ow" i=> crew Y F Γ Φ P R i
local notation "Xv" i=> bundle Y F Γ Φ P R i
variable (hE:JointE p q Y W t G K Γ)(hF:JointK p q F Φ W t G K) (h₀:P.Wave t)(hC:P.Reframe)
include hE hF hC h₀ R
set_option maxRecDepth 3000 in
set_option maxHeartbeats 500000 in
lemma banner_h (hp:straight K): PaletteT.Payment (bundle Y F Γ Φ P R) t K G q :=by
   -- Binds hE for registered entry and all-ambient color for others.
   let Xg:= Keys c N; let g:= rootR (Spine Unit) (Keys c N)
   have Hg (i:D)(U:Grid c)(j:Option I): (Xv j).read t U (R.ear i)= Reel.mist (S j) t i U:= by exact pullE P (S j) (Q j) (Ow j) i U t
   have Hf (i:E)(U:Grid c)(j:Option I): (Xv j).plug (R.tag i) U= Φ j i U:=by exact congr_fun (figuresK P _ _ (Ow j) i|>.1) U
   have Hk i (h:i∉Set.range R.ear)(U:Grid c)(j:Option I) : (Xv j).read t U i=g (P.reading t U i):= rootE P _ _ (Ow j) i h U t
   have HE i (h:i∉Set.range R.tag)(U:Grid c)(j:Option I) : (Xv j).plug i U=g (P.plug i U):=congr_fun (orientK P _ _ (Ow j) i h|>.1) _
   have HL (x:EvenA c N): Loose (P:=I) q (fun _=>g x):=by
        have hh: Polite q ∅ (g x):=by unfold Polite; rw[burst_absent]; exact ⟨_,quiet ..⟩
        exact ⟨hh,fun i=> ValidPieces.role _ hh (subset_univ _),fun _=>rfl⟩
   refine ⟨hp,toggle R.ear _ (fun i U=>?_) (fun i h V=>?_), toggle R.tag _ (fun i V=>?_) (fun i h V=>?_),toggle R.ear _ (fun i V=>?_) (fun i h V=>?_),toggle R.tag _ (fun i V=>?_) (fun i h V=>?_)⟩
   · simp_rw [Hg i U]; refine tur (fun _=>0) _ (T:=Y.z i) (Or.inl (hE.neutral ..)) (fun j=>?_ ) ?_
     · unfold Reel.mist; by_cases he:Healthy t ((S j).addr i).support U; · rw [masked_eq _ _ _ _ he]; exact ((hE.blocking j).stage i U).1
       rw [masked_ne _ _ _ _ he]; exact polite_nil ..
     intro ht; exact False.elim (((hE.blocking (none:Option I)).stays i).ne_empty ht)
   · simp_rw [Hk i h V]; exact HL _
   · simp_rw [Hf i V]; refine tur (fun _=>0) _ (Or.inl (hF.unit i V)) (T:=F.z i) (fun j=> ((hF.blocking j).budget i V).1) ?_ -- first arg
     intro he; exact False.elim (((hF.blocking (none:Option I)).commits i).ne_empty he)
   · simp_rw [HE i h V]; exact HL _
   · simp_rw [Hg]; exact hE.sense i V
   · simp_rw [Hk i h]; apply unity K _ hp; by_cases hz:Healthy t (P.row i).support V
     · unfold Rise.reading; rw [masked_eq _ _ _ _ hz,masked_eq _ _ _ _ (by unfold Healthy; rw [gauge_flags]; exact hz)]; exact Subtype.ext (root_turn G _ _ (hC.main i V G))
     unfold Rise.reading; rw [masked_ne _ _ _ _ hz,masked_ne _ _ _ _ (by unfold Healthy; rw [gauge_flags]; exact hz), map_zero,map_zero]
   · simp_rw [Hf]; exact hF.sense i V
   simp_rw [HE i h]; exact unity K _ hp _ _ (Subtype.ext (root_turn G _ _ (hC.plug i V G)))
end YM.MassiveQCD.Plette
#print axioms YM.MassiveQCD.Plette.banner_h
