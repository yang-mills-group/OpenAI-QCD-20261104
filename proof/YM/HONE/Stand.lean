import YM.HONE.Milas
import YM.Lyre.Pillar
import YM.Lyre.Price
set_option autoImplicit false
noncomputable section
namespace YM.Intag.CardsT
open Function Filter Finset MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Lat QCD.Tide Push.GridApprox
open QCD.Grass QCD.Plum
open MassiveQCD MassiveQCD.Cupola MassiveQCD.Sample Sample.LoomT Sample.Quills
open QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby
open scoped BigOperators Classical
variable {S:Scheme}{R:Side}{ℓ i k n:ℕ}{I:Type} [Fintype I] (A:Massive.Run S n R 6)
variable (X:I→ Cover) (U:I→ Averaging)(q:I→Bool)
local notation "H" k:arg=> Hole I S ℓ k
local notation "p" k:arg=> showX S ℓ k X
local notation "L" k:arg=> CardsT.link S ℓ k X
variable (w:∀ k:ℕ,Hole I S ℓ (k+1)→Hole I S ℓ k→ℝ)
variable (hw: ∀ k,ℓ ≤ k → SignedWeights S ℓ k X U (w k))
local notation "Sn"=> S.side R
set_option quotPrecheck false
variable (F:I → Cover → Insertion (S.side R n) 6) -- true ordered list tests
-- stage sensor.L.V ephemeral transport. choose left mass-density placement convention.

local notation "Pr"=>A.regulator.density
variable (hA:A.Actual)
include hA
local notation "G"=>Talent.scale (fun _i:H k=>(-1:ℝ)) (older A X U F k (ℓ:=ℓ))
local notation "Eτ" i:arg=> earnL S ℓ n i X U F
-- elementary armas. cope signs.Component
lemma inkT (t:ℕ) (s:Fin t→H k): G t s= ⇑(AllAt A k ((List.ofFn fun i=>(-((Eτ k) (s i)))).prod *Pr)):=by

   have hV : ∀ (t:ℕ)(s:Fin t→H k),(List.ofFn (fun i=>-((Eτ k) (s i)))).prod= Talent.realize (fun _i:H k=>(-1:ℝ)) s • rolledT X U F t s:=by
        intro t; induction t with
        | zero=> intro s; simp [rolledT,Talent.realize]
        | succ t ih=>
            intro s; rw [List.ofFn_succ,List.prod_cons,show (List.ofFn _).prod=_ from ih (fun i:Fin t=> s i.succ),mul_smul_comm,Talent.realize,Talent.realize,Fin.prod_univ_succ]; unfold rolledT; rw[List.ofFn_succ (n:=t),List.prod_cons, mul_smul, neg_mul,smul_neg]; norm_num [Talent.realize] -- adjust
   rw[hV,smul_mul_assoc,show rolledT X U F t s*Pr=Pr*rolledT X U F t s from DFunLike.coe_injective ?_,map_smul]
   · rfl
   have he:= Lyre.even_comm A hA (rolledT X U F t s) (le_refl n); rw [hA.start] at he; exact he.symm
variable (Ψ:I → Cover → Insertion (S.side R k) 6)
variable (hΨ:∀ (u:I)(b:Cover),∀ V:Grid (S.side R k),Hom (q u) (Ψ u b V))
noncomputable def chordR (Ψ:I → Cover → Insertion (S.side R k) 6) (g:H k):Stud (S.side R k) 6:=⇑(Ψ g.1 ((p k) g))
local notation "ψc"=>chordR X (ℓ:=ℓ) Ψ
noncomputable def egest (i:ℕ)(Ψ:I → Cover → Insertion (S.side R i) 6):Tones (S.side R i) (Hole I S ℓ i):= nurture _ (q ∘ Prod.fst) (chordR X (ℓ:=ℓ) Ψ) (Talent.scale (fun _:Hole I S ℓ i=> (-1:ℝ)) (older A X U F i)) -- includes hA?
local notation "Yb"=> egest A X U q F k Ψ (ℓ:=ℓ)
noncomputable def starL (v:H k):Stud (S.side R n) 6:= climbH A k n (chordR X (ℓ:=ℓ) Ψ v) + ⇑(-((Eτ k) v)) -- includes X
variable (f:Hole I S ℓ k→∀ i,Set (Site (S.side R i))) (hx:∀ a:Hole I S ℓ k, Plum.Fence (f a k) (chordR X (ℓ:=ℓ) Ψ a)) -- U reserved
local notation "W"=> starL A X U F Ψ
-- continuous at middle (chordR). literal.
omit hA
lemma egestF (t:ℕ)(v: Fin t→ H k): Continuous (Yb t v):=by
    let Z:=H k; have hpN (n:ℕ) (f':Fin n→ Hole I S ℓ k): Continuous (fun i=> (List.ofFn (fun j=> chordR X Ψ (f' j) i)).prod):=by
        induction n with
        | zero=> exact continuous_const
        | succ n ih=> simp only [List.ofFn_succ,List.prod_cons]; exact (ContinuousMap.continuous (Ψ (f' 0).1 ((p k) (f' 0)))).mul (ih (fun i:Fin n=> f' i.succ))
    unfold egest nurture; refine continuous_finsetSum _ fun i _=> ?_
    let y:= (List.ofFn (fun j=> chordR X (ℓ:=ℓ) Ψ (Quills.tour i j))); letI : DecidableEq (Hole I S ℓ k) := fun a b=> Classical.propDecidable _; let s:=crest v \ i; let Z:= G s.card (Quills.tour s); have hz:Continuous Z:= (ContinuousMap.continuous _).const_smul (Talent.realize (fun _i:H k=> (-1:ℝ)) (Quills.tour s)) -- may need explicit
    refine Eq.mp ?_ (Continuous.const_smul ((hpN _ (Quills.tour i)).mul hz) (spliceG (q ∘ Prod.fst) v i))
    apply congr_arg Continuous; rfl
variable (H₀:k ≤ n)
include hA H₀ hx hΨ
lemma astuteR (t:ℕ)(s:Fin t→H k) (hΘ:∀ v:H k,∀ V:Grid _,Hom (q v.1) ((Eτ k) v V))(hp:Injective s)(hP:∀ v∈ Quills.crest s,Lease k n (f v))(hd:∀ i:ℕ,k≤ i→ i<n→∀ u∈Quills.crest s,∀ v∈Quills.crest s,u≠ v→ Disjoint (f u i) (f v i)) : sig A k (Yb t s)=valueH A.regulator (List.ofFn (fun i=>starL A X U F Ψ (s i))).prod:=by
     let g:=S.multiplier R A.w k n 6; have hg:g≠0:=by apply Finset.prod_ne_zero_iff.mpr; intro i h; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hA.w_pos (mem_Ico.mp h).2).ne');
     have h' :∀ v:H k,∀ V:Grid _,Grass.Hom (q v.1) ((-((Eτ k) v)) V):=fun v V=>by rw[←neg_one_smul ℂ ((Eτ k) v)]; exact ((hΘ v V)).smul _
     have hx' := Lyre.nucleate A (q∘Prod.fst) s G Pr (fun j=> -((Eτ k) j)) ψc f hp H₀ hd hP hx (fun i hi hv=> (hA.w_pos hv).ne') (fun j=> hΨ _ _) h' (fun Qp _=>inkT A X U F hA _ _)
     have ht: A.regulator.Z=joint (A.density n):=by unfold Regulator.Z; change joint ⇑(Pr*1)=_; rw [mul_one,hA.start]
     let P:=(List.ofFn (fun i=>starL A X U F Ψ (s i))).prod
     unfold sig; rw [show joint (Yb t s)= _ from hx', Scheme.conservation S R A.density _ hA.travels H₀ (Nat.zero_le _), valueH, ht]; change g*joint (P*⇑Pr) / (g *joint (A.density n))= _; rw [← hA.start, ← Lyre.even_comm _ hA P le_rfl, mul_div_mul_left _ _ hg]; rw [hA.start]; rw [div_eq_inv_mul]; rfl -- maybe ring
omit hA H₀ hx hΨ
end YM.Intag.CardsT
#print axioms YM.Intag.CardsT.astuteR
#print axioms YM.Intag.CardsT.egestF
