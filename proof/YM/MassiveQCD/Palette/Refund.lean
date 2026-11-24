import YM.MassiveQCD.Palette.Taper
/-! # publication of the body and on-site linear columns to soft attachments
 refunds: ALL masks on received Φ. (Companion over radius later.) No uncharged costs off mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ} {a r u t σ η ξ :ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Residual
variable {ι:Type}(E:Gem c N ι)(z:Bool)(i:ι)(V:Grid c)
noncomputable def spoke (z:Bool): Gem c N ι:=⟨fun i=> ⟨(E.addr i).site,{(E.addr i).site},mem_singleton_self _⟩,fun i _=> spinCharge E z i⟩
lemma spokeG: (spoke E z).Gather:=⟨fun _ _ _ _=>rfl, fun _=>measurable_const, fun _ _=>flashPad _ (mem_singleton_self _)⟩
noncomputable def refund (z:Bool)(t:ℝ): Ruby.Hue c N ι:=⟨fun i=>(E.addr i).support,fun i V=> if Healthy t (E.addr i).support V then 0 else -(baker c N (gemTone E i)+letters (spoke E z) t V i)⟩
lemma say : (refund E z t).mean i V= letters E t V i - (letters (shadowE E z) t V i + baker c N (gemTone E i) + letters (spoke E z) t V i) :=by
    change ite _ _ _= _; by_cases h:Healthy t (E.addr i).support V
    · rw [if_pos h,letters, letters,masked_eq _ _ _ _ h, masked_eq _ _ _ _ (show Healthy t ((shadowE E z).addr i).support V from h), letters, masked_eq _ _ _ _ (h.mono_left (show ((spoke E z).addr i).support⊆(E.addr i).support from singleton_subset_iff.mpr (E.addr i).anchor))]; change 0=_- (E.view ..- (_+spinCharge ..)+_+ _); change 0=E.view i V - (E.view i V-(baker c N (gemTone E i)+spinCharge E z i) + baker c N (gemTone E i)+spinCharge E z i); abel
    rw [if_neg h,show letters E _ _ _=0 from masked_ne _ _ _ _ h,show letters (shadowE E z) _ _ _=0 from masked_ne _ _ _ _ h]; abel
lemma refundG (t:ℝ): (refund E z t).Tall t:= by
    let Δ := (refund E z t)
    have he i x: Δ.mean i x= if Healthy t (E.addr i).support x then 0 else -(baker c N (gemTone E i)+letters (spoke E z) t x i):=rfl
    refine ⟨fun i V U hv hU=> ?_,?_,fun i U h ht=> h (if_pos ht),?_⟩
    · have hA : Healthy t (E.addr i).support V ↔ Healthy t (E.addr i).support U:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty, show (E.addr i).support ∩ flags t V= (E.addr i).support ∩ flags t U from hU, ← Finset.disjoint_iff_inter_eq_empty]
      rw [show _= _ from he i V,he i U]; apply if_congr hA rfl; exact congr_arg (fun x:EvenA c N=> -(baker c N (gemTone E i)+x)) (Work.H03.reads_larger (show ((spoke E z).addr i).support⊆(E.addr i).support from singleton_subset_iff.mpr (E.addr i).anchor) (clearUse _ i ((spokeG E z).sees i) _) V U hv hU)
    · intro i; refine Measurable.ite (healthy_closed _ _).measurableSet measurable_const ?_; exact (measurable_const.add (RG.masked_measurable t _ _ ((spokeG E z).reads i))).neg -- binder
    intro i U; rw [show _=_ from he i U]; split; next _=> exact Fleet.spruce _
    next _=>
       have hf : Gated ((Δ).bud i) (baker c N (gemTone E i)+letters (spoke E z) t U i):=by
           unfold Gated; rw [map_add]; exact Subalgebra.add_mem _ (Reggae.gates ..) (gateMon _ _ (show ((spoke E z).addr i).support⊆Δ.bud i from singleton_subset_iff.mpr (E.addr i).anchor) _ (licit _ (spokeG E z) _ U))
       unfold Gated; rw [map_neg]; exact Subalgebra.neg_mem _ hf
lemma spokeInk (hv:Noted E) : Noted (spoke E z):=by
    refine ⟨fun i=> flashColor _ _, fun i _=> shut E z i,?_⟩ -- fix
    intro i U; have h:Regal c N _= _:= (rank_ink E z i hv).2.1; change Regal c N (_+spinCharge ..)= _+_ at h; rw [map_add,Reggae.through] at h; exact add_left_cancel h
-- oriented prices. preserve grading externally via given perm.
lemma voyager (s:Strut c)(k:Spike)(g:Site c→ℂ)(e:Equiv.Perm ι) (h:E.addr (e i)=rotateL (E.addr i) s)(hV:∀ V:Grid c,Diode N s k g (E.view i (sky s V))= E.view (e i) V) (hv:Noted E) (he:Warrant s g k)(hG:Gated (E.addr i).support (E.view i 1))(V:Grid c): Diode N s k g ((refund E z t).mean i (sky s V))=(refund E z t).mean (e i) V:=by
    obtain ⟨ht,hk⟩:= era E z s g k e i h hV hv he hG; let U:= (E.addr i).support; let W:= (spoke E z)
    have hp: (flags t (sky s V)).image (act s)=flags t V:=Work.H03.flags_send ..; have h0: ((spoke E z).addr (e i)).support=((spoke E z).addr i).support.image (act s):=by change {(E.addr (e i)).site}= image _ {(E.addr i).site}; rw [h,image_singleton]; rfl
    have h1 : Diode N s k g (letters W t (sky s V) i) = letters W t V (e i):=sprayer t ((W.addr i).support) ((W.addr (e i)).support) (W.view i) (sky s V) V _ _ (h0.symm ▸ shadesU t ((spoke E z).addr i).support (W.view i) _ _ _ hp) hk.symm
    change Diode N s k g (if Healthy .. then _ else -(baker _ _ _+letters W t _ _))= if Healthy .. then _ else _; rw [apply_ite (Diode N s k g)]; apply if_congr ?_ (map_zero _) ?_
    · exact h.symm ▸ shadesU t U (E.view i) (sky s V) V _ hp
    rw [map_neg,map_add,h1,Reggae.through,ht]
lemma refundWire (t:ℝ)(hv:Noted E): (∀ i,shadeG ((refund E z t).mean i)) ∧ (∀ i U,AccentFit ((refund E z t).mean i U)) ∧ ∀ i U, Regal c N ((refund E z t).mean i U)=(refund E z t).mean i U:=by
    have h := spokeInk E z hv; let W i:= (refund E z t).mean i; let P:= (spoke E z)
    have he (i:ι)(u:EvenA c N→+*EvenA c N)(V U:Grid c)(hp: flags t V=flags t U)(hk:u (spinCharge E z i) = spinCharge E z i)(hr:u (baker c N (gemTone E i))=baker c N (gemTone E i)): u (W i V)=W i U:=by
          change u (if Healthy .. then _ else -(baker c N _+letters P t V _))=if Healthy .. then _ else _
          rw [apply_ite u]; apply if_congr (show Healthy t (E.addr i).support V↔_ by unfold Healthy; rw [hp]) (map_zero _); rw [map_neg,map_add,hr]; suffices hg:u (letters P t V i)=letters P t U i by rw [hg]
          exact sprayer t ((P.addr i).support) _ _ V U _ _ (by unfold Healthy; rw [hp]) hk -- args
    exact ⟨fun i U g=> congr_arg Subtype.val (he i (sways (Lat.rotates N g)) _ _ (gauge_flags .. ) (Subtype.ext (h.gauge i U g)) (Reggae.through ..)), fun i U g hg=> he i _ U U rfl (h.num i U g hg) (Reggae.through ..),fun i U=>he i _ U U rfl (h.real i U) (Reggae.through ..)⟩
end YM.QCD.Stew.Phased
