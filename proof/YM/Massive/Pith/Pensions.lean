import YM.Massive.Pith.Shelves
import YM.Massive.Commerce.Issue
/-! # Remnant. No site change; through-3 improvement for iterative bank. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false -- parallel unfold cases
noncomputable section
namespace YM.QCD.Pith
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Revolve Stew Reggae Brick Port Entr
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
variable (b:Flavor N)
local notation "J"=> Modes c N
variable {t r q:ℝ}{p:BudgetPoint}{ι α β:Type}
variable (o:Site c) (M:Spike)

variable (E:Gem c N ι)
-- payout.
def dusting : Gem c N ι:= ⟨ E.addr, fun i x=> E.view i x-tallyShelf E i⟩
variable (i:ι)(U:Grid c)
lemma renown (h:Woven (E.addr i).site (E.addr i).support p t (E.view i) r)(hp:0<t): Woven (E.addr i).site (E.addr i).support p t ((dusting E).view i) ((2+jointFee N)*r):=by
    refine (Loom.Wminus _ _ h ((sewBudget E i h hp).addition (shelfBudget E i h hp))).stretches (Subset.refl _) (le_of_eq ?_)
    ring
variable {f:ι→ℝ} {x':ℝ}
lemma dignify (h:Licence p t r x' E)(hz:0<x'): Licence p t ((2+jointFee N)*r) x' (dusting E):=by
    obtain ⟨f,hf,h⟩:=h.zone; refine ⟨fun i=>(2+jointFee N)*f i, ?_,fun i=>renown E i (h i) hz⟩
    exact Shells.valued_mult (X:=E.addr) (f:=f) hf (by positivity [joint_valid N])
variable (h:CrossP E)(he:E.Gather)
-- shelf incl price independent of volume even before reanchor. winding Berm.
include h
lemma zero_mud : Reggae.mud ((dusting E).view i 1)=0:=by
    let v:= sewShelf E i; change clay c N (E.view i 1-_)=_
    have he:clay c N (E.view i 1-v)=0:= chooseP _ (h.real i 1)
    rw [tallyShelf,← sub_sub,map_sub,he,show clay c N (lampShelf E i)=0 from mud_lamp E i,sub_zero]
omit h in
lemma residue (hV:Nonwrapping (E.addr i).support (E.addr i).site) : shape (E.addr i).site (feeF b ((dusting E).view i 1)) none=0:=by
    change profile _ none (meter b (E.view i 1-(sewShelf E i+lampShelf E i)))=0
    rw [map_sub,map_add,show meter b (sewShelf E i)=0 from reduceF b _,zero_add,map_sub,show profile _ none (meter b (lampShelf E i))=_ from chartShelf b E i]; unfold Stew.lane Stew.mote; rw [if_pos hV]; exact sub_self _
include he
-- carry by permutation supplied customer grade independent
omit h he in
lemma sew_turn {w : Equiv.Perm ι} {Z:Spike} (_hp : Warrant v g Z) (hm:∀ i,Diode N v Z g (E.view i (sky v (1:Grid c)))=E.view (w i) 1): Diode N v Z g (sewShelf E i)=sewShelf E (w i) := by
    have h0: sky v (1:Grid c)=1:=by ext1 i; simp [Strut.sky,pull,Step.read]
    let P:=Diode N v Z g; rw [sewShelf,sewShelf,←hm i,h0]; rw [mur,Reggae.thorough ..]
lemma transfer (w : Equiv.Perm ι)(P : Spike)(hp:Warrant v g P)(hv:∀ i,E.addr (w i)= rotateL (E.addr i) v ∧ ∀ U, Diode N v P g (E.view i (sky v U))= E.view (w i) U) : Diode N v P g (tallyShelf E i)=tallyShelf E (w i):= (map_add (Diode N v P g) _ _).trans (congr_arg₂ HAdd.hAdd (sew_turn E i hp fun i=> (hv i).2 1) (turn_lamp E i hp (w i) (hv i).1 (h.num i 1) (hv i).2 (h.gauge _) (he.role _ _)))
lemma sparkleM (w : Equiv.Perm ι)(P : Spike)(hp:Warrant v g P)(hv:∀ i,E.addr (w i)= rotateL (E.addr i) v ∧ ∀ U, Diode N v P g (E.view i (sky v U))= E.view (w i) U) : Diode N v P g ((dusting E).view i (sky v U))=(dusting E).view (w i) U:= (map_sub (Diode N v P g) _ _).trans (congr_arg₂ _ ((hv i).2 U) (transfer E i h he w P hp hv))
lemma snowy : CrossP (dusting E):=by
    refine ⟨fun i V k=>?_, fun i V=>?_,fun i V=> ?_, fun v k g hp=>?_⟩
    · refine congr_arg Subtype.val (show sways (Lat.rotates N k) ((dusting E).view i (gauge k V))=(dusting E).view i V from ?_); unfold dusting tallyShelf sewShelf; dsimp only; rw [map_sub,map_add, Reggae.thorough ..,gauge_lamp E]; exact congr_arg₂ HSub.hSub (Subtype.ext (h.gauge i V k)) rfl
    · apply phase_sub (h.num i V) ; refine phase_add (fun _ _=> Reggae.thorough ..) (phase_lamp E i) -- eta problem
    · unfold dusting tallyShelf sewShelf; dsimp only; rw [map_sub,map_add,Reggae.thorough ..,Regal_lamp E i h]; exact congr_arg₂ HSub.hSub (h.real i V) rfl
    obtain ⟨w,hw⟩:= h.rays v k g hp; exact ⟨w,fun i=>⟨(hw i).1,fun U=> sparkleM E i U h he w k hp hw⟩⟩
lemma fleckIssue (hz:0<t)(hw:Woven (E.addr i).site (E.addr i).support p t (E.view i) r)(hV:Nonwrapping (E.addr i).support (E.addr i).site) : Dust.Fleck p (E.addr i).support (E.addr i).site true ((dusting E).view i) t ((2+jointFee N)*r):=by
    have hp:=renown E i hw hz; let T:=dusting E; have hT:=snowy E h he
    have hR : Reggae.river c N (T.view i 1)=0:=by change -(Reggae.mud _).re=_; rw [zero_mud E i h]; simp
    refine ⟨hp,hT.gauge i,hT.real i,fun _=>?_, (spores _ _ _ hp (hT.gauge _) hz.le).1, (E.addr i).anchor,hR⟩
    rw [octave,hR,map_zero,sub_zero]; exact Brick.at3 _ _ (hT.num i 1) (hT.gauge i) (fun b=> residue b E i hV)
end YM.QCD.Pith
#print axioms YM.QCD.Pith.fleckIssue
