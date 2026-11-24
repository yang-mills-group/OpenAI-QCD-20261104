import YM.QCD.Pant.Ambit
/-! # split sym E. no perlabel rotation assumptions, conserve total. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Patron
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
local notation "V"=>EvenA c N
variable {t:ℝ}
-- emerald/ruby separate.
structure Gem (n:Side) (F:ℕ) (ι:Type) where
 addr : ι→RegularAddress n
 view : ι→Grid n→EvenA n F
structure Rail (n:Side)(F:ℕ)(ι:Type) where
 addr : ι→ Cove.Hat n
 warp : ι→Grid n→EvenA n F
variable {ι β:Type} (E:Gem c N ι)(J:Rail c N β)
structure Gem.Gather (E:Gem c N ι):Prop where
 sees j: LocalOn (E.addr j).support (E.view j)
 reads j: Measurable (E.view j)
 role j (U):Gated (E.addr j).support (E.view j U)
structure Rail.Reg (E:Rail c N ι) (t:ℝ):Prop where
 uses j: UsesFinal t (E.addr j).place (E.warp j)
 reads j:Measurable (E.warp j)
 role j(U):Gated (E.addr j).place (E.warp j U)
 buys j(U): E.warp j U ≠0→ flags t U ∩ (E.addr j).place=(E.addr j).inv
structure Dyed (E:Gem c N ι):Prop where
 gauge i: shadeG (E.view i)
 num i U: Fit (E.view i U)
 real i U: Regal _ _ (E.view i U)=E.view i U
structure MixedP (E:Rail c N ι):Prop where
 gauge i: shadeG (E.warp i)
 num i U: Fit (E.warp i U)
 real i U: Regal _ _ (E.warp i U)=E.warp i U
 moves s z k : Warrant s z k→∃ e: Equiv.Perm ι,∀ i,
               ((E.addr (e i)).place=(E.addr i).place.image (act s)) ∧ (E.addr (e i)).inv=(E.addr i).inv.image (act s) ∧∀ U:Grid c, Diode N s k z (E.warp i (sky s U))= E.warp (e i) U -- c N vs binder arity here if `E: Rail c N ι`
noncomputable def duo : Rise c N ι β:=⟨E.addr,J.addr,E.view,J.warp⟩
lemma regimen (h:E.Gather)(hp:J.Reg t): (duo E J).Wave t:=⟨h.sees,h.role,h.reads,hp.uses,hp.role,hp.reads,hp.buys⟩
abbrev spice (z: Strut c):= Diode N z (sat z) (ink z)
def averageC (c:Side):ℝ:=(Fintype.card (Strut c):ℝ)⁻¹
noncomputable def rotateL (p: RegularAddress c)(v:Strut c) : RegularAddress c:=⟨act v p.site,p.support.image (act v), mem_image_of_mem _ p.anchor⟩
abbrev ManyA (c:Side)(ι:Type):= Strut c × ι
def glean : Gem c N (ManyA c ι) where
 addr v:=rotateL (E.addr v.2) v.1
 view i U:=averageC c • spice i.1 (E.view i.2 (sky i.1 U))
lemma mellow (h:E.Gather):(glean E).Gather:=by
   constructor
   · rintro ⟨z,j⟩ U W he; refine congr_arg (averageC c • ·) (congr_arg (spice z) (h.sees j (sky z U) (sky z W) (agrees_pull z.1 z.2 he)))
   · rintro ⟨z,i⟩; exact measurable_const.smul ((show Measurable (spice z (N:=N)) from (phare _).measurable).comp ((h.reads i).comp (continuous_pull ..).measurable))
   rintro ⟨v,k⟩ U; exact Territory.club _ _ _ (gateS v _ _ _ _ (h.role k _))
lemma dyed (h:Dyed E): Dyed (glean E):=by
   constructor
   · rintro ⟨v,i⟩ U k
     suffices he : sways (Lat.rotates N k) ((glean E).view (v,i) (gauge k U))=(glean E).view (v,i) U by exact congr_arg Subtype.val he
     let P:= spice v (N:=N); change sways _ (averageC c • _) = averageC c • _; rw [eSM _ (phare _),show sky v (gauge k U)=gauge (k ∘ act v) (sky v U) from pull_gauge ..]; apply congr_arg; unfold spice
     rw [custodial k _ (assured v)]; apply congr_arg; exact Subtype.ext (h.gauge i (sky v U) (k ∘ act v))
   · rintro ⟨v,k⟩ U; exact dated _ _ (polarizei _ (h.num k _) _)
   rintro ⟨v,k⟩ U; exact dolled _ (Diode N v _ _ _) ((gammaT _ (h.num k _) (assured v)).trans (congr_arg _ (h.real k _)))
lemma pantR [Countable ι] [Countable β] (h:Dyed E)(hp: MixedP J) (t:ℝ) : Villa.Pant c N t (duo (glean E) J):=by
   have he:= dyed E h
   refine ⟨⟨he.gauge,hp.gauge⟩, ?_, fun U=> Villa.permanence _ _ _ (fun i U=> he.real i U) (fun i U=>hp.real i U) U,fun W hv U=> Villa.permanence _ _ _ (fun i U=> he.num i U W hv) (fun i U=> hp.num i U W hv) U⟩
   intro v g k hh
   obtain ⟨e,hp⟩:= hp.moves _ _ _ hh
   refine ⟨Equiv.prodCongr (skyEquiv v) (Equiv.refl _),e,fun U=>⟨Work.H03.flags_send ..,?_,?_,fun i=> (hp i).1,fun i=> (hp i).2.1,?_,fun i=> (hp i).2.2 U⟩⟩ -- note Equiv.refl count required
   · rintro ⟨p,i⟩; change ((E.addr i).support.image (act (pod v p)))=((E.addr i).support.image (act p)).image (act v); rw [podA,image_image]; rfl
   · rintro ⟨p,i⟩; exact Equiv.congr_fun (podA v p) _
   rintro ⟨p,i⟩; change Diode N v k g (averageC c • spice p (E.view i (sky p (sky v U))))= averageC c • spice (pod v p) (E.view i (sky (pod v p) U)); rw [skying,eSM _ (phare _)]; apply congr_arg; change sways _ (sways _ _)=_; rw [leaps,← copies_mul,← beset _ _ _ _ g (ink p)]; exact coinT (E.view i _) (h.num i _) (comb hh (assured p)) (assured _) -- ABC order inspect

def letters (t:ℝ)(U:Grid c)(i:ι):= masked t (E.addr i).support (E.view i) U
def total (t:ℝ)(U:Grid c):= ∑' i, letters E t U i
lemma shapeS (U:Grid c) (z:Strut c)(i:ι): letters (glean E) t U (z,i)= averageC c • spice z (letters E t (sky z U) i):=by
    unfold letters; have hh : Healthy t ((glean E).addr (z,i)).support U ↔ Healthy t (E.addr i).support (sky z U):= healthy_pull ..; by_cases h:Healthy t (E.addr i).support (sky z U)
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (hh.mpr h)]; rfl
    rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt hh.mp h), map_zero,smul_zero]
lemma ocean (h : ∀ U,Summable (letters E t U))(hp:∀ z:Strut c, ∀ U,spice z (total E t (sky z U))=total E t U)(U:Grid c) : HasSum (letters (glean E) t U) (total E t U):=by
    let f:= letters (glean E) t U; let g z i:= averageC c • spice z (letters E t (sky z U) i)
    let p:= total E t U
    have he(z) : HasSum (fun i=> f (z,i)) (averageC c • p):=by
       have hx:= ((h (sky z U)).hasSum.map (spice z) (phare _)).const_smul (averageC c); have hh : HasSum (g z) (averageC c • spice z (total E t (sky z U))):=hx; rw [hp] at hh; exact hh.congr_fun (fun i=> shapeS E U z i)
    have hp':(∑ z:Strut c, averageC c • p)=p:=by
       unfold averageC; rw [sum_const,← Nat.cast_smul_eq_nsmul ℝ,card_univ,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
    rw [show total E t U=p from rfl, ← hp']; exact Beam.lapis f _ he
end YM.QCD.Patron
