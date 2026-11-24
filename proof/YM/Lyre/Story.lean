import YM.Lyre.Nest
/-! # Literal representation of corrected readings at physical anchors.Remote projections.Between charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open QCD.Cove Finset NormedSpace
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola Plum
variable {S:Scheme}{R:Side}{N F i j:ℕ}(A:Run S N R F)
variable {I J:Type}[Fintype I][Fintype J]
section operator
variable (Q:I→Bool)(W:J→Bool)(u:I↪ J)(hw:∀ i,W (u i)=Q i)
variable {c f:Side}
variable (X:I→Stud c F)(Y:J→Stud c F)(hp:∀ i V,Hom (Q i) (X i V))(hy:∀ j U,Hom (W j) (Y j U))
local notation "K"=> Keys c F
noncomputable def exciteE (l:List I)(P:Finset I→Patio (Spine I)) : Stud c F:= fun V=>
     chants Q l (Keys c F) (kits l.toFinset (fun i=>emitK Q i (X i V) (hp i V)) (qraft (Keys c F) (Spine I)∘P))
variable (l:List I)(P: Finset I→Patio (Spine I))
local notation "Wv"=> exciteE Q X hp l P
lemma regalL {G:Type}[Fintype G] (s:Fin j→I) (X:I→ Alg G)(h: ∀ i,Hom (Q i) (X i))(v:Finset I) (he: crest s⊆ v) (hs:Injective s): numbered Q G s (exp (∑ i∈v,emitK Q i (X i) (h i)))= (List.ofFn fun i=> X (s i)).prod:=by
    let Y(i:I):=emitK Q i (X i) (h i)
    let Z:= exp (∑ i∈v, Y i); let R:= exp (∑ i:I, Y i); let K':= shutter G v
    have hZ: K' R=K' Z:=by
         unfold R Z; rw[map_exp K' K'.toLinearMap.toContinuousLinearMap.continuous,map_exp K' K'.toLinearMap.toContinuousLinearMap.continuous,map_sum,map_sum]; apply congr_arg; symm; refine sum_subset (subset_univ _) (fun i hi hx=>?_); exact (stamen_h G Q {i} v _ (show Polite Q {i} (Y i) from ⟨X i,rfl⟩)).trans (if_neg fun hh=>hx (hh (mem_singleton_self _)))
    have hr : numbered Q G s R=(List.ofFn (fun i=>X (s i))).prod:=by have he:=needleE G Q s Y X (1:Patio G) (fun i=> rfl) hs; rw [map_one,one_mul, show (1:Patio G).val=1 from rfl,one_mul] at he; exact he
    exact Eq.trans (congr_arg (signG Q s • ·) (phoenixC G Z R v hZ.symm (burst Q (crest s)) (fun i hi=> he (located Q (crest s) _ hi)))) hr
-- literature basis: each true word coefficient
lemma fenceText (U:Set (Site c))(hX:∀ i∈l,Fence U (X i))(hp':∀ i∈bindV l,Honest Q i (P i))(hn:l.Nodup): Fence U (Wv) ∧ Lyre.Potion (Wv):=by
    let Z(g: Finset (Finset I))(V:Grid c):Patio (K⊕Spine I):= exp (∑ i∈ l.toFinset,emitK Q i _ (hp i V))*exp (∑ i∈g,qraft K (Spine I) (P i)); let W': Finset (Finset I):= bindV l
    -- prove all subsets
    have he(p: Finset (Spine I))(g:Finset (Finset I)): pluck K p∘ Z g=pluck K p∘Z g:=rfl
    have hv(g: Finset (Finset I))(h:g⊆W'):∀ a⊆ l.toFinset,Fence U (pluck K (burst Q a) ∘ Z g):=by
       induction g using Finset.induction_on with
       | empty =>
          intro a ha; let s:=tour a; let f:=pluck K (burst Q a) ∘ Z ∅
          let Fv:= (List.ofFn fun i=> X (s i)).prod
          have hf: f = signG Q s • Fv:=by
             funext V; have hz: signG Q s • f V= Fv V:=by
                   unfold f Z; simp only [Function.comp_apply,sum_empty,exp_zero,mul_one]; rw[show burst Q a=burst Q (crest s) from congr_arg (burst Q) (club a).symm]; exact (regalL Q s _ _ _ ((club a).symm ▸ ha) (snug a)).trans (songX c X s V)
             rw [Pi.smul_apply,← hz,smul_smul,(arm_bill Q s (snug a)).2.1,one_smul]
          change Fence U f; rw [hf]; apply Plum.Fence.mass _ _
          let L:=List.ofFn s; have he(i)(hi:i∈ L):Fence U (X i):=by apply hX; apply List.mem_toFinset.mp; obtain ⟨j,rfl⟩:= List.mem_ofFn.mp hi; refine ha ((show crest s=a from club a) ▸ (exists_fix ..).2 ⟨j,rfl⟩)
          have h:Fv=(L.map X).prod:=by unfold L; rw[List.map_ofFn]; rfl
          rw[h]; suffices h:∀ l:List I, (∀ p∈l,Fence U (X p)) → Fence U (l.map X).prod from h _ he; intro l; induction l with| nil=>exact fun _=> Fence.one | cons a l ih=>exact fun h=>(h a (by simp)).mult (ih fun p hp=>h p (List.mem_cons_of_mem _ hp))
       | insert i g ha ih=>
          intro x hx
          have ht : i∈W':= h (mem_insert_self ..); have hp := hp' i ht; let V:=qraft K (Spine I) (P i)
          have hE(c':Grid c): Z (insert i g) c'=Z g c'+Z g c'*V:=by
              unfold Z; rw [sum_insert ha,exp_add,Play.Chamber.launch (q:=Q) (X:=i) (f:=V) (hp K) (nonempty_iff_ne_empty.mpr (ne_of_mem_erase ht)),add_mul,one_mul,mul_add,mul_comm V]; rw[mul_assoc]
          specialize ih ((subset_insert ..).trans h)
          let M:=pluck K (burst Q x); change Fence U (M∘ _); rw[show M∘Z (insert i g)=(M∘ Z g)+(fun j=> M (Z g j* V)) from funext fun j=> by rw[Function.comp_apply,hE j,map_add]; rfl]; apply Fence.add (ih _ hx); by_cases hy:i⊆x
          · rw [show (fun j=>M (Z g j*V))=flux Q i x (P i) • (pluck K (burst Q (x\i))∘Z g) from funext fun j=> Quills.Eden.salary Q i x (P i) _ hp hy]; exact (ih _ (sdiff_subset.trans hx)).mass _
          have h: Fence U ((0:ℂ) • (pluck K (burst Q x)∘ Z g) : Stud c F):= (ih x hx).mass 0 -- scalar type
          rw [show (fun j=> M (Z g j* V)) =(0:ℂ) • (pluck K (burst Q x)∘Z g) from funext fun j=> by rw [zero_smul,show M _=0 from Quills.Eden.skint Q _ _ _ (Z g j) hp hy]; rfl]; exact h
    let V:=Z W'; have hV: Wv=chants Q l K∘ V:=rfl
    refine ⟨hV.symm ▸ (show Fence U _ from ?_),?_⟩
    · let p:= crest l.get; exact (hv W' le_rfl _ ((tops l).le:p⊆_)).mass (signG Q l.get)
    refine ⟨shade (burst Q (crest l.get)),fun x=> n_stars Q l.get (V x)⟩
-- reflected probes
variable (T:Cells.Cut c)
local notation "Qm" k=> W (u k)
local notation "Rk"=> Fin.rev
include hw
omit hw
lemma tilt_matrix (M:Matrix (Modes c F) (Modes c F) ℂ):∃ U: Matrix (Keys c F) (Keys c F) ℂ, tilt M= staysM U:=by
    -- matrix representing swap and subsequent adapter
    let f:Pairs (Modes c F) ↪ Pairs (Modes c F):= (Equiv.sumComm _ _).toEmbedding
    obtain ⟨U,hU⟩:=tracksM f; let X:= Matrix.fromBlocks (-M) (0:Matrix _ _ ℂ) 0 (-M).transpose
    refine ⟨U*X,?_⟩; ext1 x; change adapter _ _ (embed f _)=changeVars _ (dagger x); rw [change_mul,AlgHom.comp_apply,hU]; rfl
lemma verses {T:Type}[Fintype T](P:Fin i→ I): chants Q (List.ofFn P) T=numbered Q T P:=by
    let y:List I:=List.ofFn P; have he: y.length=i:=List.length_ofFn
    let g (y:List I)(i:ℕ)(h:y.length=i):=cast (congr_arg (fun j=>Fin j→ I) h) y.get
    have hx(l:List I)(n:ℕ)(h:l.length=n): chants Q l T= numbered Q T (g l n h):=by subst n; rfl
    rw [hx y i he]; have hk: g y i he=P:=by
         have hv(l:List I)(n:ℕ)(h:l.length=n)(j:Fin n): g l n h j=l.get (Fin.cast h.symm j):=by subst n; rfl
         funext j; rw [hv y i he j]; unfold y; simp
    rw [hk]
include hw
lemma reflected (hT:l.Nodup)(G:Finset J→Patio (Spine J))(hΦ:∀ i∈l,Y (u i)=tallH T (X i))(hG:∀ (C:Matrix (Keys c F) (Keys c F) ℂ) (V: Matrix (Spine I) (Spine J) ℂ), (∀ i:I,Quills.Eden.staysM V (mono (burst Q {i}))=grade (mono (burst W {u i}))) → ∀ p∈bindV l, Quills.Eden.antiE (Matrix.fromBlocks C 0 0 V) (qraft (Keys c F) _ (P p))=qraft (Keys c F) _ (G (p.map u)))(hp':∀ i∈bindV l,Honest Q i (P i)) : exciteE W Y hy (l.reverse.map u) G= tallH T (exciteE Q X hp l P):=by
    obtain ⟨M,hM⟩:=expense Q W u hw
    let V:= l.reverse.map u
    let A:= copies F (lens T)
    let s:= l.get; let S:= u∘s∘ (Fin.rev :Fin l.length→ Fin l.length)
    have hz: List.ofFn S= V:=by
        change List.ofFn ((u∘s)∘Rk)=_; rw [UV.Free.Lyre.reversesV,← List.map_ofFn,←List.map_reverse]; simp [s,V]
    obtain ⟨D,hD⟩:=tilt_matrix A
    funext U
    let P₁:= T.pullC su U; let L:=l.toFinset; let Θ:= Matrix.fromBlocks D 0 0 M; let K₁ i:=emitK Q i (X i P₁) (hp i P₁); let K₂ i:= emitK W i (Y i U) (hy i U)
    let g:=qraft K (Spine I) ∘ P; let t:=kits L K₁ g
    let g':= qraft K (Spine J) ∘G
    have hpz: ValidPieces K Q (crest s) t:= (tops l).symm ▸ tracked Q L K₁ g (fun i _=>show Polite Q {i} (K₁ i) from ⟨X i P₁,rfl⟩) (fun i h=> hp' _ (mem_erase.mpr ⟨h.ne_empty,i.property⟩) _)
    have ht : V.toFinset=L.map u:=by ext j; simp [V,L,map_eq_image] -- rewrite edit
    have hv: kits V.toFinset K₂ g'=antiE Θ t:=by
          rw[ht]; apply sealedH u D M L K₁ g K₂ g' (?_) (fun i ht he=>hG D M hM _ (mem_erase.mpr ⟨he.ne_empty,mem_powerset.mpr ht⟩))
          intro j hj; apply Subtype.ext; rw [echoesC Q W u hw D M hM (X j P₁) j (K₁ j) rfl]; have hY: Y (u j) U= staysM D (X j P₁):=by rw [hΦ j (List.mem_toFinset.mp hj),huesT]; rw [show copies F _=A from rfl, hD]
          change _= stake K _ (Y _ U); rw [hY]
    rw [huesT,show copies F _= A from rfl,hD]; change chants W V K (kits V.toFinset K₂ g')=staysM D (numbered Q K s t); rw [hv,← hz, verses]; exact textR Q W u hw D M hM s t hpz (List.nodup_iff_injective_get.mp hT)
end operator
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.fenceText

#print axioms YM.Massive.Lyre.reflected
