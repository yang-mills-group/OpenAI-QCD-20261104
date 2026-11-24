import YM.MassiveQCD.Evolution.Capture
/-! # Paying forced cuts after reaching ALL real powers
 Family assemblies use exactly one choice per support-spectrum st at each stencil.
 No multiplicity losses from flag groups by pretending to pair choices freely. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open MassiveQCD.Analysis.Shelf Metric
variable {c:Side}{N n B:ℕ}{t s r δ T τ u :ℝ}{i:Site c} {ι : Type}
local notation "Ω"=> EvenA c N
variable (p:Patron.Rail c N ι)
namespace Gather
abbrev Ways (ι:Type):=Finset (ι×ℕ)
def stage (t:Ways ι):= t.image Prod.fst
variable (F: Patron.Rail c N (ι×ℕ)) (ht:F.addr=p.addr ∘ Prod.fst)
section refine
variable (X:Finset ι)
abbrev Word (X:Finset ι):= ↥X → ℕ
noncomputable def entryP (s:Word X):stage ⁻¹' ({X}: Set (Finset ι)) := by
   let u:Ways ι:=Finset.univ.image (fun k:↥X=> (k.val,s k)); exact ⟨u,(show stage u = X from Finset.ext fun i=>by simp [stage,u])⟩
lemma enter_mem (s:Word X)(i:ι)(n:ℕ): (i,n)∈(entryP X s).val↔ ∃ hi : i ∈ X,n=s ⟨i,hi⟩:=by simp [entryP,eq_comm]
lemma entry_inj: Injective (entryP X):=by
    intro x y hi; funext i; have hx: (i.val,x i)∈(entryP X x).val:=(enter_mem ..).2 ⟨i.2,rfl⟩; rw [hi] at hx; obtain ⟨hg,h⟩:= (enter_mem ..).1 hx; exact h
include ht
lemma entryAlive (w:stage ⁻¹' ({X}: Set (Finset ι))) (h: separated (blocked (home F)) w.val) : w∈ Set.range (entryP X):=by
    let w':= w.val; have hw: stage w'=X:= w.2
    have he(i:↥X):∃ n:ℕ,(i.val,n)∈ w':=by
        have hm:i.val∈ w'.image Prod.fst:= by exact Eq.subst (motive:=fun S=> i.val∈ S) hw.symm i.2
        obtain ⟨⟨p,n⟩,ht,h⟩:=mem_image.mp hm; exact ⟨n,(show p=i.val from h) ▸ ht⟩
    have hx (i:ι) (n m:ℕ)(hv:(i,n)∈w')(hu:(i,m)∈w'): n=m:= by
        by_contra hk; obtain ⟨j,hj⟩:= (p.addr i).alive.mono (p.addr i).part; have h:(w':Set (ι×ℕ)).PairwiseDisjoint (home F):= (GasP.close _ _ _).1 h; let T:=Finset.disjoint_left.mp (show Disjoint .. from h hv hu (fun h=> hk (congr_arg Prod.snd h)))
        have hg(w:ℕ):home F (i,w)= (home p) i:= congr_arg Cove.Hat.place (congr_fun ht _); change j∈home p i at hj; exact T ((hg n).symm ▸ hj) ((hg m).symm ▸ hj)
    choose g hg using he; refine ⟨g,Subtype.ext (Finset.ext ?_)⟩; rintro ⟨i,n⟩; rw [enter_mem]; refine ⟨fun ⟨h,hF⟩=>hF.symm ▸ hg ⟨i,h⟩,fun hv=>?_⟩
    have hi:i∈ X:=hw ▸ mem_image_of_mem Prod.fst hv; exact ⟨hi,hx i n _ hv (hg ⟨i,hi⟩)⟩
lemma suitLife (s:Word X): separated (blocked (home p)) X↔ separated (blocked (home F)) (entryP X s).val:=by
    have he (i:ι)(w:ℕ):home F (i,w)=home p i:=congr_arg Cove.Hat.place (congr_fun ht (i,w)); rw [GasP.close,GasP.close]; constructor
    · rintro hv ⟨i,n⟩ h₁ ⟨j,m⟩ h₂ hj; obtain ⟨ha,hV⟩:=(enter_mem ..).1 h₁; obtain ⟨hu,hT⟩:=(enter_mem ..).1 h₂; change Disjoint _ _; rw [he,he]; exact hv ha hu (fun h=> hj (by subst j; rw [hV,hT]))
    intro hv i hi j hj hd; let a:=(i,s ⟨i,hi⟩); let b:=(j,s ⟨j,hj⟩); change Disjoint _ _; rw [← he i a.2, ← he j b.2]
    exact hv (show _ from (enter_mem X s i a.2).2 ⟨hi,rfl⟩) (show _ from (enter_mem X s j b.2).2 ⟨hj,rfl⟩) (fun h=> hd (congr_arg Prod.fst h))
lemma sphereMark (s: Word X) : (entryP X s).val.biUnion (oriD F) = X.biUnion (oriD p):=by
   have he (i:ι)(w:ℕ):oriD F (i,w)=oriD p i:=congr_arg Cove.Hat.inv (congr_fun ht (i,w)); ext i; simp only [mem_biUnion]; constructor
   · rintro ⟨⟨i,p⟩,hi,hj⟩; obtain ⟨h,_⟩:= (enter_mem ..).1 hi; exact ⟨i,h,he .. ▸ hj⟩ -- syntax
   rintro ⟨i,h,hh⟩; exact ⟨(i,s ⟨i,h⟩),(enter_mem ..).2 ⟨_,rfl⟩,(he i _).symm ▸ hh⟩ -- witness implicit
omit ht in
lemma peakS (s: Word X)(U:Grid c): (∏ i∈(entryP X s).val,F.warp i U) = ∏ i:↥X,F.warp (i.val,s i) U:=by
    refine (prod_image ?_).trans rfl; -- syntax
    intro a _ b _ h; exact Subtype.ext (congr_arg Prod.fst h)
omit ht in
lemma harvest {A B:Type}[Fintype A](y:A→B→ Ω)(p:A→ Ω)(h:∀ i,HasSum (y i) (p i)) (hg:Summable (fun s:A→ B=>∏ i:A, y i (s i))) : HasSum (fun s:A→ B=>∏ i:A,y i (s i)) (∏ i:A,p i):=by
    let F (x:Finset B) := Fintype.piFinset (fun _ : A=>x)
    have hf : Tendsto F atTop atTop:= by
        refine tendsto_atTop.2 ?_; intro z; filter_upwards [eventually_ge_atTop (z.biUnion (fun s:A→B=> Finset.univ.image s))] with b hb; intro i hi; exact Fintype.mem_piFinset.mpr (fun a=>hb (mem_biUnion.mpr ⟨i,hi,mem_image_of_mem _ (mem_univ _)⟩)) -- signature
    have hx:= tendsto_finsetProd (s:= (univ:Finset A)) (fun i _=> (show Tendsto (fun s: Finset B=> ∑ j∈s, y i j) atTop _ from h i))
    have hm : ∀ s:Finset B,(∑ i∈ F s,∏ j:A, y j (i j))=∏ j:A,∑ i∈s,y j i:= fun s=> (Finset.prod_univ_sum _ _).symm
    -- equality of two `𝓝 bound` values via eventually total.
    let p (s:A→ B):=∏ i:A,y i (s i); have he: Tendsto (fun s:Finset B=>∑ i∈ F s,p i) atTop (𝓝 (∑' i,p i)):= Tendsto.comp (g:=fun s:Finset (A→ B) => ∑ j∈s,p j) (f:=F) (show Tendsto (fun s:Finset (A→ B) => ∑ j∈s,p j) atTop _ from hg.hasSum) hf -- name conflict p. goal
    simp_rw [p,hm] at he; rw [← tendsto_nhds_unique he hx]; exact hg.hasSum
include ht
lemma wind (t:ℝ)(U:Grid c)(hs:∀ i,HasSum (fun n=> F.warp (i,n) U) (p.warp i U))(hU: Summable (tK F t U)) : HasSum (fun i:stage ⁻¹' ({X}: Set (Finset ι))=>tK F t U i.val) (tK p t U X):=by
    have hx:= entry_inj X; let G (i:stage ⁻¹' ({X}: Set (Finset ι))):=tK F t U i.val; change HasSum G _; have he : Summable G:= hU.comp_injective (Subtype.val_injective)
    apply (hx.hasSum_iff (fun i hi=>?abs)).mp
    case abs=>
       unfold G tK; split; next hp=> exact (hi (entryAlive p F ht X i hp.1)).elim
       next _=> rfl
    let f(i:Word X):= G (entryP X i)
    by_cases h:separated (blocked (home p)) X ∧ flags t U=X.biUnion (oriD p)
    · have hp (i): f i=∏ j:↥X,F.warp (j.val,i j) U:=by unfold f G tK; rw [if_pos ⟨(suitLife p F ht X i).1 h.1,h.2.trans (sphereMark p F ht X i).symm⟩,peakS]
      change HasSum f _; let M (i:Word X):=∏ j:↥X,F.warp (j.val,i j) U; have hM : f=M:=funext hp; have hm₁ : Summable f:= he.comp_injective hx
      rw [hM,tK,if_pos h,← prod_coe_sort X]; exact harvest (A:=↥X) (B:=ℕ) (fun i n=>F.warp (i.val,n) U) (fun i=>p.warp i.val U) (fun i=> hs i.val) (show Summable M from hM ▸ hm₁)
    have hh(i): f i=0:=by unfold f G tK; rw [sphereMark p F ht X i, ← suitLife p F ht X i,if_neg h]; -- zeros
    change HasSum f _; rw [funext hh,tK,if_neg h]; exact hasSum_zero
end refine
end Gather
end YM.QCD.Ruby
