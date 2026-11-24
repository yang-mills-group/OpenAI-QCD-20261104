import YM.QCD.Agate.Trine
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f G K L: Side}{F i j:ℕ}{β t:ℝ} {D Y:Lot}
open Tide Flume YM.Next.Free Kites
-- fallback matrix projector always exists
noncomputable def gather {A B:Type*}[Fintype A][Fintype B](u:A→B):Dirac B→ₐ[ℂ] Dirac A:= changeVars (Matrix.of (fun i j=> if (Sum.map u u) j=i then 1 else 0))
lemma stashed {A B:Type*}[Fintype A][Fintype B](u:A↪ B): (gather u).comp (pass u)=AlgHom.id ℂ _:=by
    refine ext_atoms fun i=>?_ ; unfold gather; rw [AlgHom.comp_apply]; change changeVars _ (embed (Sum.map u u) (atom i))=_; rw [embed_atom,change_atom]; simp [(Sum.map_injective.mpr ⟨u.injective,u.injective⟩).eq_iff,ite_smul] -- error
noncomputable def keel (p:Site c)(h:Fits c D): Pad D F↪Modes c F:=⟨pens p,pensI p h⟩
lemma garner (p:Site c)(h:Fits c D): LeftInverse (gather (pens p)) (pass (pens p (D:=D) (F:=F))):= fun x=> AlgHom.congr_fun (stashed (keel p h)) x
lemma reign (p:Site c)(h:Fits c D): Injective (pass (pens p (D:=D) (F:=F))):= (garner p h).injective
noncomputable def starlet (p:Site c)(x:Trace D):Grid c:=Function.extend (strike p) x 1
lemma spar (p:Site c)(h:Fits c D): RightInverse (starlet p) (crest (D:=D) p):= fun i=> funext fun _=> (crested p h).extend_apply ..
lemma shrew (p:Site c)(hw:Fits c D): Continuous (starlet (D:=D) p):=by
    apply continuous_pi; intro i; by_cases hp:∃ j:Pipe D,strike p j=i
    · obtain ⟨j,rfl⟩:= hp; simp_rw [show ∀ x:Trace D,starlet p x (strike p j)= x j from fun i => (crested p hw).extend_apply ..]; exact continuous_apply _
    have h(u:Trace D): starlet p u i=1:=Function.extend_apply' u _ _ hp; simp_rw [h]; exact continuous_const
lemma stateG (p:Site c)(h:Fits c D)(Z:Paper D F)(hp:Tide.Stays (jewel p Z))(hx:Tide.Neutral (jewel p Z)): Z∈political D F:=by
    have hh: Z=fun i:Trace D=> gather (pens p (D:=D) (F:=F)) (jewel p Z (starlet p i)):=by funext i; unfold jewel; rw [spar p h i,garner p h]
    refine ⟨?_,?_⟩
    · conv => arg 1; rw [hh]
      exact (hp.travel ((shrew p h).measurable)).flows ((gather (A:=Pad D F) (pens p)).toLinearMap.continuous_of_finiteDimensional)
    intro k U; let T: Frame c:= Function.extend (pins h p) k 1; have he: (fun i:Court D=>T (leap p i.val))=k:= funext fun i=> (pins h p).injective.extend_apply ..; let V:= starlet p U; have hw:crest p V= U:= spar p h U
    have H:= hx T V; rw [jewelT] at H; dsimp only at H; rw [he] at H; unfold jewel at H; simp only [hw] at H; exact reign p h H
lemma reading (p:Site c)(h:Fits c D): Injective (Agate.visit (F:=F) (D:=D) p):=by
    intro i j e; apply Subtype.ext; funext u; have he:=congr_fun e (starlet p u); change jewel p i.val _= jewel p j.val _ at he; unfold jewel at he; rw [spar p h] at he; exact reign p h he
variable (P:Flight i i)(W: KernelChoices)(h:f.val=c.val*P.L.val) (p:Site c)(β t:ℝ)
variable (hP:Fits c D)(hc: Fits f (rimH D P.patch))(hp:P.patch.Branches W su)
lemma popping (x:Paper D F)(V:Trace D): let v:=x V; patternC _ _ t (pass (pens p) v)=pass (pens p) (engine t _ v):=by
    intro v; rw [← Grass.write v]; simp only [map_smul,map_sum]; refine sum_congr rfl fun i _=> congr_arg ((coef i v) • ·) ?_; unfold patternC; rw [nominate (mono i) t _ (homogeneous i),map_smul]; exact (nominate _ _ _ (pass_layer _ (homogeneous _)))
noncomputable def inkH (x:Paper D F)(t:ℝ):Paper D F:=fun V=> engine t _ (x V)
lemma piles(x:Paper D F): stampC (jewel p x) t=jewel p (inkH x t):=by funext i; exact popping p t x (crest p i)
noncomputable def aris (x:Paper D F)(U:Grid f): Poly (rimH D P.patch) F := furnace ((ater P h U).submatrix (pens p) (pens ((sliceL P h).embed p))) (brook (P.visit W h) β (inkH x t⁻¹∘ crest p) U)
include hP hc hp
lemma swivel (x:Paper D F)(hx:Tide.Stays x)(U:Grid f): look P W h β t (jewel p x) U=pass (pens ((sliceL P h).embed p)) (aris P W h p β t x U):=by
    unfold look offer; rw [piles]; let B:=inkH x t⁻¹; let S:=P.visit W h; have he:B=inkH x t⁻¹:=rfl; rw [← he];
    have hv:Tide.Stays (B∘crest p):= (hx.travel ((crestC p).measurable)).flows ((engine t⁻¹ _).toLinearMap.continuous_of_finiteDimensional)
    let q:= (sliceL P h).embed p
    let M:= ((pass (pens (D:=D) (F:=F) p)).toLinearMap.toContinuousLinearMap).restrictScalars ℝ; rw [show brook (P.visit W h) β (jewel p B) U= M (brook S β (B∘crest p) U) from (bruM (S:=S) hp _ hv M _ _ id (MeasurePreserving.id (prior su c)) (fun _=>rfl)).symm]; unfold aris; convert! excite (M:=ater P h U) (keel (F:=F) p hP) (keel (F:=F) q hc) (fun _ _ h1=> sight P h _ _ h1) (brook S β (B∘crest p) U) using 1 -- instance mismatch
    unfold furnace; simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,AlgHom.toLinearMap_apply]; congr 6; exact Subsingleton.elim .. 
noncomputable def arborn (x:Paper D F):Paper (rimH D P.patch) F:= fun U=>aris P W h p β t x (starlet ((sliceL P h).embed p) U)
variable {z:Site G} (H:K.val= G.val*P.L.val)(hx:Fits G D)(hd:Fits K (rimH D P.patch))(ht:stoke ((sliceL P h).embed p) (rimH D P.patch))(hu:stoke ((sliceL P H).embed z) (rimH D P.patch))
include ht
include hx hd hu
lemma victory (x:Paper D F)(hX:Tide.Stays x): look P W H β t (jewel z x)=jewel ((sliceL P H).embed z) (arborn P W h p β t x):=by
     funext U; rw [swivel P W H z β t hx hd hp x hX]; let v:= (sliceL P H).embed z; let q:= (sliceL P h).embed p; let V:= starlet q (crest (D:=rimH D P.patch) v U)
     have hK: crest (D:=rimH D P.patch) q V=crest v U:= spar q hc _
     have he:Tide.Stays (inkH x t⁻¹):=hX.flows ((engine _ _).toLinearMap.continuous_of_finiteDimensional)
     let L (z:ℂ):=z
     change pass _ _ = pass _ (aris P W h p β t x V); symm; unfold aris; rw [unite P h z H hP hx hK hp _ he]; apply congr_arg; exact congr_arg (fun M: Matrix (Pad D F) (Pad (rimH D P.patch) F) ℂ=> furnace M (brook (P.visit W H) β (inkH x t⁻¹∘ crest z) U)) (Matrix.ext (fun i j=> startled P h z H p hc hd ht hu hK i j))
omit hx hd hu
lemma honorable (x:Malt D F): arborn P W h p β t x.val∈political (rimH D P.patch) F:=by
     apply stateG ((sliceL P h).embed p) hc
     · rw [← victory P W h p β t hP hc hp h hP hc ht ht x.val (staysP x)]; exact lookup _ _ hp _ (palps p x).hp
     rw [← victory P W h p β t hP hc hp h hP hc ht ht x.val (staysP x)]; exact rolly P h hp _ (paysA _ (palps p x).hp) (stageN _ (jewelN p x))
end YM.QCD.Agate
