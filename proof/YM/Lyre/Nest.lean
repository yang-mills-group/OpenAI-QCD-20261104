import YM.Lyre.Bloom
import YM.Lyre.Packs
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open Transfer QCD.Cove
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
variable {S:Scheme}{R:Side}{N F i j:ℕ}(A:Run S N R F)
local notation "gR"=> S.side R
local notation "Pv" k=> S.step k
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola Plum Finset NormedSpace
variable (hA:A.Actual)
section
open FlareV
variable {I:Type}[Fintype I](Q:I→Bool)(t:ℂ) (Y:I→ Stud (S.side R i) F)
-- Pulse data already equal relative to A via §Tera scaling.S.Product with q required homogeneous.
variable (E:Grid (S.side R j)→Patio (Keys (S.side R j) F⊕Spine I))
variable (f: ∀ k,Set (Site (S.side R k)))
-- marked startup budget.Mag moments.Bond statement: `t:Tera'`.*Reel.E all configs.This may not be zero.Ht.
variable (r:I→ℝ)(hp:∀ a:I,∀ V,Hom (Q a) (Y a V))(hS:∀ a:I,Stays (Y a))(U: I→ (k:ℕ)→ Set (Site (S.side R k)))(hv:∀ a : I,Lease i N (U a))(hg:∀ a : I,Uses (U a i) (Y a))(he:∀ a:I,Neutral (Y a)) (hd:∀ k:ℕ,i≤k→ k<N → ∀ a : I,∀ b : I,a≠b→Disjoint (U a k) (U b k))
variable (hi:i≤N)(hn:j ≤ i)
variable (hz:∀ (k:ℕ)(s:Fin k→I),Injective s→Quills.crest s ⊆ univ→ let Z:= (numbered Q (Keys (S.side R j) F) s ∘ E) ; Stays Z ∧ t*sig A j Z = give r (Quills.crest s) *sig A i (A.density i * (List.ofFn fun a=> Y (s a)).prod))
-- unweighted launch gardens at bare pulls for each a; valid any activated tiling.A. Does not require Continuity after. Define corrected exact carrier. Momentum.Z ports.Matches.
include hp hi
variable {J:Type}(l:List J) (V:J→List I) (G:Finset I→ Patio (Spine I)) (hG:∀ i∈ allV l V,Honest Q i (G i))(w:I→ℝ)
local notation "En"=>epochN A hA Q Y hp hS hi
local notation "C"=> Keys (gR j) F
local notation "D"=> Keys (gR N) F
local notation "IG"=>Spine I
noncomputable def tokenV (v:List I)(G: Finset I→ Patio (Spine I)): Stud (S.side R N) F:= fun X=> chants Q v (Keys (S.side R N) F) (kits v.toFinset (radiant A Q Y hp hS hi X) (qraft D (Spine I) ∘ G))
include hA hv hg he hd hi hz hG
-- universal per pressure.Word retrieval theorem. including footprints arc.
lemma realms (hV:(l.flatMap V).Nodup)(hU:(l.flatMap V).toFinset=univ):
     let g(i:Finset I):ℂ:=give w i *give r i; let z:= allV l V
     let f(i:Finset I):=g i • qraft (Keys (S.side R j) F) (Spine I) (G i);
     let F₀ := fun X=>capstone (Keys (S.side R j) F) w (E X)* NormedSpace.exp (∑ i∈z,f i)
     let u:= chants Q (l.flatMap V) (Keys (S.side R j) F) ∘ F₀; let s:= (l.map (fun z=> tokenV A Q Y hp hS hi (V z) G)).prod
     Stays u ∧ t*sig A j u=(g univ)*valueH A.regulator s:=by
    intro g z f F₀ v' s; let W':=capstone D r ∘ En; let Q':=univ (α:=I)
    obtain ⟨P,hP⟩:= pricedL A hA j N t 1; have heq : VoiceL Q Q' P E W':=by
         apply by_read Q _ P; intro n s hs hx; change _∈ (P:Set (Stud (gR j) F × Stud (gR N) F)); rw [hP]; exact epitome A hA Q Q' t Y E r hp hS U (fun a _=>hv a) (fun a _=> hg a) he (fun j hx he' a _ b _=>hd j hx he' a b) hi hz s hs hx -- args
    let Wp(i:Finset I):= g i • G i; have hW : VoiceL Q Q' P (capstone C w∘E) (capstone D w ∘ W'):= standingL _ _ _ P _ _ heq
    have hx:=treatments Q Q' P (capstone C w ∘ E) (capstone D w∘ W') hW z Wp (fun i hi=> ⟨fun T h=>by unfold Wp; rw[map_smul]; exact ((hG i hi) _).smooch _,(city l V _ hi).1⟩)
    let L:= l.flatMap V; let a:= L.get
    have h₂(i:Finset I):f i=qraft C IG (Wp i):=(map_smul ..).symm
    let G':=exp (∑ i∈ z,qraft D IG (Wp i))
    let Ω := numbered Q D a ∘ fun i=> capstone D w (W' i)*G'
    have hp': (v',Ω)∈ P:=by
        unfold v' chants F₀; simp_rw [h₂]; exact to_read Q Q' _ P _ _ hx (subset_univ ..)
    have hQ : Ω=g Q' • (s*A.density N):=by
         funext V'; unfold Ω; rw[Function.comp_apply]; let K:= radiant A Q Y hp hS hi V'; let T:= qraft D IG ∘ G; let X: Patio D:=⟨A.density N V',hA.even le_rfl V'⟩
         have H0:= correcting l V K T X Q hV hU (fun k=>⟨climbH A i N (Y k) V',rfl⟩) (fun i hi=>hG i hi _) r w
         simp_rw [G', Wp, map_smul]; change chants Q _ _ _= _; rw[show capstone D w (W' V') =capstone D w (capstone D r (rootR IG D X* exp (∑ i:I,K i))) from rfl]; change _=(g Q' • _ :Stud (gR N) F) V'; refine Eq.trans H0 (?_); rw[Pi.smul_apply,Pi.mul_apply]
         let Yv j:=tokenV A Q Y hp hS hi (V j) G
         have hs(p:List J): (p.map (fun j=> chants Q (V j) D (kits (V j).toFinset K T))).prod=(p.map Yv).prod V':=by induction p with| nil=> rfl|cons a l ih=> rw[List.map_cons,List.map_cons,List.prod_cons,List.prod_cons, ih]; rfl
         erw [hs l]
    rw [hQ] at hp'; replace hp':(v',g Q' • (s*A.density N))∈ Accord A j N t 1:= (by rw [← hP]; exact hp'); obtain ⟨h₁,h₂,h₃⟩:=hp'; refine ⟨h₁,?_⟩; change t*_ =1 * sig A N _ at h₃; rw[h₃,one_mul,sig_smul A hA]; rw[← even_comm A hA s le_rfl]; congr 1; unfold sig; simp_rw [valueH,rawK,hA.start]; let R:=A.regulator; have he:R.Z=joint (A.density N):=by unfold Regulator.Z; change joint ⇑(R.density*1)=_; rw [mul_one,hA.start];
    change _=(A.regulator.Z)⁻¹* _; rw [he,hA.start]; exact div_eq_inv_mul ..
end
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.realms
