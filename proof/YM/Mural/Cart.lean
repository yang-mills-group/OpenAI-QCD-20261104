import YM.Mural.Bus
/-! # fibers and transfer: commute geometry on the metric bound, cost by all endpoint choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat PaletteT Ribbon Push.AbsoluteSums
variable {c f:Side}{j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
open Massive Massive.PCAC
-- resolve all Mode reads across Ω order
abbrev Dye (N:ℕ):= Pinor × Flavor N
abbrev idx (x:Site c)(i:Dye N)(z:Hue) : Modes c N:= ((x,(i.1,z)),i.2)
def cargo (X:PCAC.Deck c N)(x y:Site c)(i j:Dye N)(z:Rank):= X (idx x i z.1) (idx y j z.2)
variable (L:YM.Next.Free.Flight j k)(d:f.val=c.val*L.L.val)(K:KernelChoices)(β w:ℝ)(hk:L.patch.Branches K su)
local notation "sV"=> Transfer.blockMap L K d β w hk
set_option quotPrecheck false
local notation "A"=>arctic L.L j
local notation "F"=> (L.visit K d).ratio
variable (x y: Site c)(i j':Dye N)(u v:Site f)
local notation "sQ"=>texel L d (0:Site f) x u
local notation "sJ"=>texel L d (0:Site f) y v
-- single Matrix port collapses only selections matching fixed spin flavor. 
lemma hingeQ (p q:Dye N)(z e:Hue)(W:Grid f): qmove L d N W (idx x p z) (idx u q e)= if p=q then sQ W z e else 0:=by
    rw [show qmove _ _ _ _ _ _=_ from stencil L d x u W N (p.1,z) (q.1,e) p.2 q.2,activeP]; split
    · rename_i h; split
      · rename_i e; rw [if_pos (Prod.ext e h)]
      next he=> rw [if_neg (fun (h:p=q)=>he (h ▸ rfl))]
    next hf=> rw [if_neg (fun (h:p=q)=>hf (h ▸ rfl))]
lemma bearer (i₁ i₂:Dye N)(M:PCAC.Deck f N)(a b:Rank)(W:Grid f):
     berth L d (idx u i₁ b.1) (idx v i₂ b.2) (idx x i a.1) (idx y j' a.2) (cargo M u v i₁ i₂ b) W= if (i,j')=(i₁,i₂) then doll (sQ W) (sJ W) a b • cargo M u v i j' b W else 0:=by
       change (qmove L d N W (idx x i a.1) (idx u i₁ b.1)*star (qmove L d N W (idx y j' a.2) (idx v i₂ b.2))) • (cargo M u v i₁ i₂ b W)=_; rw [hingeQ,hingeQ]; by_cases H:i=i₁ <;> by_cases H': j'=i₂
       · subst i₁; subst i₂; rw [if_pos rfl,if_pos rfl,if_pos rfl]; rfl
       all_goals simp [H,H']
-- an equivalence aligns pair-product orders
noncomputable def modesV (N:ℕ)(c:Side): (Site c × Dye N × Hue) ≃ Modes c N:=
  ⟨fun i=>idx i.1 i.2.1 i.2.2, fun i=> (i.1.1,(i.1.2.1,i.2),i.1.2.2),fun i=>rfl,fun i=>rfl⟩
noncomputable def grouped (N:ℕ)(c:Side): (((Site c × Site c) × (Dye N × Dye N) × Rank)) ≃ Modes c N × Modes c N:=
   ({ toFun:= fun i=> ((i.1.1,i.2.1.1,i.2.2.1),(i.1.2,i.2.1.2,i.2.2.2)), invFun:=fun i=> ((i.1.1,i.2.1),(i.1.2.1,i.2.2.1),(i.1.2.2,i.2.2.2)), left_inv := fun _=>rfl, right_inv :=fun _=> rfl}:(((Site c×Site c)×(Dye N× Dye N) × Rank))≃ _).trans (Equiv.prodCongr (modesV N c) (modesV N c))
variable (M:PCAC.Deck f N)
local notation "Qx"=> Quilt L K d β w hk
noncomputable abbrev sphereK : Rank→Insertion c N:= billow L d K w β hk x y u v (cargo M u v i j')
local notation "KT"=> ((Site f×Site f))
noncomputable def ringV (p: Site f×Site f): Prop:= separation p.1 p.2≤berthD j ∧ separation ((L.visit K d).ratio.embed x) p.1 ≤ arctic L.L j ∧ separation ((L.visit K d).ratio.embed y) p.2≤arctic L.L j
noncomputable abbrev choiceV:= Finset.univ.filter (ringV L d K x y)
lemma touchpoint : cargo (Qx M) x y i j'= ∑ k:KT, billow L d K w β hk x y k.1 k.2 (cargo M k.1 k.2 i j'):=by
    ext1 p; let S:= idx x i p.1; let U:=idx y j' p.2; let m(j:Modes f N × Modes f N):= berth L d j.1 j.2 S U (M j.1 j.2)
    let H(k:KT):=(haul L d x y k.1 k.2 (cargo M k.1 k.2 i j') p); have he:∀ k:KT,(∑ i:(Dye N×Dye N) × Rank,m (grouped N f (k,i)))=H k:=by
         intro k; ext1 V; rw [ContinuousMap.sum_apply,Fintype.sum_prod_type,sum_eq_single (i,j')]
         · apply sum_congr rfl; intro j hj; exact (bearer L d x y i j' k.1 k.2 i j' M p j V).trans (if_pos rfl)
         · exact fun b hb h=> sum_eq_zero fun j _=> (bearer L d x y i j' k.1 k.2 b.1 b.2 M p j V).trans (if_neg h.symm)
         simp
    change sV (∑ i,m i)=_; rw [← (grouped N f).sum_comp m,Fintype.sum_prod_type]; simp_rw [he]; rw [map_sum,Finset.sum_apply]; exact sum_congr rfl fun _ _=> rfl
variable (h:∀ p q:Site f,berthD j<separation p q→∀ i j':Dye N,cargo M p q i j'=0)
include h
lemma off_point (p:KT)(hp:p∉choiceV L d K x y): billow L d K w β hk x y p.1 p.2 (cargo M p.1 p.2 i j')=0:=by
    by_cases he: separation p.1 p.2≤ berthD j; swap; · rw [h _ _ (by omega),map_zero]
    have ht: arctic L.L j< separation ((F).embed x) p.1∨ arctic L.L j< separation ((F).embed y) p.2:=by contrapose! hp; exact mem_filter.mpr ⟨mem_univ _, he,hp⟩
    let X:= cargo M p.1 p.2 i j'; ext1 v; change sV (ascend L d x y _ _ X v)=0; refine (congr_arg sV (show ascend L d x y _ _ X v=0 from ?_)).trans (map_zero _)
    ext1 U; change (∑ i:Rank,doll (texel L d 0 x p.1 U) (texel L d 0 y p.2 U) v i • X i U)=0; apply sum_eq_zero; intro i _; unfold doll; rcases ht with hh|hh; simp [dormant L d (0:Site f) x p.1 U hh]; simp [dormant L d (0:Site f) y p.2 U hh]
lemma quiltV : cargo (Qx M) x y i j'=∑ k∈ choiceV L d K x y,billow L d K w β hk x y k.1 k.2 (cargo M k.1 k.2 i j'):= (touchpoint L d K β w hk x y i j' M).trans (sum_subset (subset_univ _) fun j _ hP=>off_point L d K β w hk x y i j' M h j hP).symm
omit h
lemma faded (hx:berthD j<separation x y): choiceV L d K x y=∅:=by apply Finset.not_nonempty_iff_eq_empty.mp; rintro ⟨s,hV⟩; obtain ⟨h1,h₂,h₃⟩:= ((mem_filter.mp hV).2 : _ ∧ _); exact not_lt_of_ge (orbitB L d x y s.1 s.2 h₂ h₃ h1) hx
lemma census : (choiceV L d K x y).card≤ ((A+A+1)^4*(berthD j+berthD j+1)^4:ℕ) :=by -- need Nat.
   let W:= choiceV L d K x y; let T:=halo A {(F).embed x}; let V(p:Site f):= halo (berthD j) {p}
   have hv: W= T.biUnion (fun i=> W.filter (fun j=>j.1=i)):= by
       ext i; constructor; · intro h; obtain ⟨_,hp,hr⟩:=((mem_filter.mp h).2 : _ ∧ _); exact mem_biUnion.mpr ⟨_,halo_spec.mpr ⟨_,mem_singleton_self _,hp⟩,mem_filter.mpr ⟨h,rfl⟩⟩
       intro h; obtain ⟨_,_,h⟩:=mem_biUnion.mp h; exact (mem_filter.mp h).1
   have hy :T.card ≤ (A+A+1)^4:=by simpa using (Lattice.Corona.halo_size ({(F).embed x}) A)
   let z:= (berthD j+berthD j+1)^4; have hz(i): (V i).card ≤z:=by simpa only [card_singleton,one_mul] using (Lattice.Corona.halo_size {i} (berthD j))
   suffices H: W.card ≤ ∑ _∈T,z from H.trans (by rw [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ hy)
   conv_lhs=>rw [hv]
   refine (Finset.card_biUnion_le ..).trans (sum_le_sum (fun i _=>?_))
   refine (Finset.card_le_card (t:={i}×ˢ V i) ?_).trans (by rw[card_product,card_singleton,one_mul]; exact hz i); intro k hk; obtain ⟨hh,hk⟩:=mem_filter.mp hk; obtain ⟨h1,h2⟩:=((mem_filter.mp hh).2 : _ ∧ _); refine mem_product.mpr ⟨mem_singleton.mpr hk,halo_spec.mpr ⟨i,mem_singleton_self _,(?_)⟩⟩; exact (hk ▸ h1)
end YM.QCD.Comet
#print axioms YM.QCD.Comet.census
#print axioms YM.QCD.Comet.touchpoint
