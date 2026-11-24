import YM.QCD.Pant.Inlet
/-! # Soft-log connector to hard ticket occurrences only -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β:Type}
-- Soft credits equivalent compressed weighted quota
structure Hue (c:Side) (N:ℕ)(ι: Type) where
  bud : ι→Support c
  mean : ι → Grid c→EvenA c N
variable (Y:Hue c N ι) (X:Rail c N β)
structure Hue.Tall (Y:Hue c N ι)(t:ℝ) :Prop where
  bond i : UsesFinal t (Y.bud i) (Y.mean i)
  meas i : Measurable (Y.mean i)
  non i U : Y.mean i U≠0→ ¬Healthy t (Y.bud i) U
  lives i U: Gated (Y.bud i) (Y.mean i U)
structure Hue.Garish (Y:Hue c N ι) :Prop where
  gauge i: shadeG (Y.mean i)
  real i U: Regal c N (Y.mean i U)=Y.mean i U
  number i U : Fit (Y.mean i U)
  travel s k g: Warrant s g k→∃ e, Got Y.bud e (act s)∧∀ (i:ι) (U: Grid c), Diode N s k g (Y.mean i (sky s U))=Y.mean (e i) U -- change forall
abbrev Stamp (ι β:Type) := β ⊕ ι
abbrev Cart (ι β:Type) := Finset (Stamp ι β)
def home (X:Rail c N β): β→Support c:= fun i=> (X.addr i).place
def oriD (X:Rail c N β): β→Support c:= fun i=> (X.addr i).inv
def footD : Stamp ι β→ Support c:=Sum.elim (home X) Y.bud
-- numeral bookkeeping
variable {Y X}
def badgeK (X:Rail c N β)(i:Cart ι β): Support c:=i.toLeft.biUnion (oriD X)
def scopeK (Y:Hue c N ι)(X:Rail c N β)(i:Cart ι β) := i.biUnion (footD Y X)
def suit (Y:Hue c N ι)(X:Rail c N β) (i:Cart ι β):Prop:= separated (blocked (home X)) i.toLeft ∧ ∀ j∈ i.toRight,¬Disjoint (Y.bud j) (badgeK X i)
def gemD (Y:Hue c N ι)(X:Rail c N β)(i:Cart ι β): Prop:= suit Y X i ∧ i.toLeft.Nonempty ∧ Ac.Spark (footD Y X) i
def sparkY (Y:Hue c N ι)(U:Grid c)(i:ι):=NormedSpace.exp (Y.mean i U) -1
def flower (Y:Hue c N ι)(X:Rail c N β)(U:Grid c): Stamp ι β→ EvenA c N:= Sum.elim (fun i=> X.warp i U) (sparkY Y U)
def tK (X:Rail c N β)(t:ℝ)(U:Grid c)(i:Finset β): EvenA c N:=if separated (blocked (home X)) i ∧ RG.flags t U=i.biUnion (oriD X) then ∏ j∈i,X.warp j U else 0
lemma duskX (E:Gem c N β)(X:Rail c N ι)(s:ℝ)(U:Grid c): (duo E X).dusk s U=tK X s U:=by funext i; unfold Rise.dusk tK; apply if_congr (and_congr ?_ Eq.comm) rfl rfl; exact (GasP.close _ _ _).symm
variable (Y X)
-- always using new equality at same flags
noncomputable def payer (t:ℝ)(U:Grid c)(s:Cart ι β):EvenA c N:= if RG.flags t U∩ scopeK Y X s=badgeK X s then ∏ i∈s, flower Y X U i else 0
abbrev Plot (Y:Hue c N ι)(X:Rail c N β):= {s: Cart ι β // gemD Y X s}
lemma badge_ne (i:Plot Y X): (badgeK X i.val).Nonempty := by
    obtain ⟨x,hx⟩:= i.2.2.1; exact (X.addr x).alive.mono (subset_biUnion_of_mem _ hx)
lemma badge_s (i:Cart ι β): badgeK X i ⊆ scopeK Y X i :=by
    intro j hj; obtain ⟨u,hu,hj⟩:=mem_biUnion.mp hj; exact mem_biUnion.mpr ⟨.inl u,mem_toLeft.mp hu,(X.addr u).part hj⟩
noncomputable def Trail (t:ℝ): Rail c N (Plot Y X):= ⟨fun s=>⟨scopeK Y X s.val,badgeK X s.val,badge_ne Y X s,badge_s Y X s.val⟩,fun i U=>payer Y X t U i.val⟩
lemma ettle (U:Grid c)(v: Finset (Stamp ι β))(ht:Y.Tall t)(hs:X.Reg t):Gated (scopeK Y X v) (payer Y X t U v):=by
   unfold payer; split
   · apply gate_prod; intro i hi; refine gateMon (footD Y X i) _ (subset_biUnion_of_mem _ hi) _ ?_
     rcases i with i|i; · exact hs.role i _
     apply gate_exp; exact ht.lives ..
   unfold Gated; rw [map_zero]; exact Subalgebra.zero_mem _
lemma plant (p:Y.Tall t)(hp:X.Reg t): (Trail Y X t).Reg t:=by
   constructor
   · intro i U V he hV; change _∩_= _ at hV; change payer .. = payer ..; unfold payer; apply if_congr
     · exact (show (flags t U∩scopeK Y X i.val=badgeK X i.val ↔ _ ) from by rw [inter_comm,show scopeK _ _ _ ∩ flags t U= _ from hV,inter_comm];rfl)
     · apply prod_congr rfl; intro j hj; have hh:footD Y X j⊆ scopeK Y X i.val:= subset_biUnion_of_mem _ hj
       rcases j with j|j; · exact Work.H03.reads_larger hh (hp.uses j) U V he hV
       change sparkY _ _ _= _; unfold sparkY; rw [Work.H03.reads_larger hh (p.bond j) U V he hV];rfl
     exact rfl
   · intro i; change Measurable (fun U=>payer Y X t U i.val); unfold payer; apply Measurable.ite _ _ measurable_const
     · let M:=scopeK Y X i.val; let k:=badgeK X i.val
       rw [show {U:Grid c| flags t U ∩ M=k}= ⋃ j∈(univ.filter (fun i:Support c=>i∩M=k)),{U|flags t U=j} by ext; simp]; exact MeasurableSet.iUnion (fun i=>MeasurableSet.iUnion (fun _=> flags_measurable_eq ..))
     exact Finset.measurable_fun_prod _ fun i _=> by cases i with | inl i=> exact hp.reads i | inr i=> exact (NormedSpace.exp_continuous.measurable.comp (p.meas i)).sub measurable_const
   · exact fun i U=>ettle Y X U i.val p hp
   intro i U h; exact by_contra fun hh=> h (if_neg hh)
end YM.QCD.Ruby
