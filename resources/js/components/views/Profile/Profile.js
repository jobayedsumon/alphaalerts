import React, {useEffect, useState} from 'react'

import {Link, useNavigate, useParams} from "react-router-dom";
import {
    CButton,
    CCard,
    CCardBody,
    CCardHeader,
    CCol,
    CForm,
    CFormInput,
    CFormLabel, CFormSelect,
    CInputGroup, CModal, CModalBody, CModalFooter, CModalHeader, CModalTitle,
    CRow
} from "@coreui/react";
import fetchWrapper from "../../helpers/fetchWrapper";
import {swalError, swalSuccess} from "../../helpers/common";
import {useDispatch, useSelector} from "react-redux";
import countries from "../../helpers/countries";
import CIcon from "@coreui/icons-react";
import {cilCheckCircle} from "@coreui/icons";


const Profile = () => {
    const navigate = useNavigate();
    const dispatch = useDispatch();

    const [user, setUser] = useState(useSelector(state => state.user));

    const [visible, setVisible] = useState(false);

    useEffect(() => {
        fetchWrapper.get('/api/user').then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                setUser(data.user);
                dispatch({type: 'set', user: data.user});
            }
        }).catch((error) => {

        });
    }, [])

    const handleSubmit = (e) => {
        e.preventDefault();

        const name = e.target.name.value;
        const email = e.target.email.value;
        const country_code = e.target.country_code.value;
        const phone_number = e.target.phone_number.value;

        fetchWrapper.put('/api/profile', {
            name: name,
            email: email,
            country_code: country_code,
            phone_number: phone_number,
        }).then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                swalSuccess("Profile updated successfully");
                setUser(data.user);
                dispatch({type: 'set', user: data.user});
                navigate('/profile');
            } else {
                swalError("Error updating profile");
            }
        }).catch((error) => {
            swalError("Error updating profile");
        });
    }

    const verificationCode = () => {
        fetchWrapper.post('/api/verification-code').then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                setVisible(true);
            } else {
                swalError("Error sending verification code");
            }
        }).catch((error) => {
            swalError("Error sending verification code");
        });
    }

    const verifyPhoneNumber = (e) => {
        e.preventDefault();

        const verification_code = e.target.verification_code.value;

        fetchWrapper.post('/api/verify-phone-number', {
            verification_code: verification_code,
        }).then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                swalSuccess("Phone number verified successfully");
                setUser(data.user);
                dispatch({type: 'set', user: data.user});
                setVisible(false);
                navigate('/profile');
            } else {
                swalError("Error verifying phone number");
            }
        }).catch((error) => {
            swalError("Error verifying phone number");
        });
    }

    const emailVerification = () => {
        fetchWrapper.post('/api/email-verification').then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                swalSuccess(data.message);
            } else {
                swalError("Error sending email verification link");
            }
        }).catch((error) => {
            swalError("Error sending email verification link");
        });
    }

    return (
        <>
            <CCard>
                <CCardHeader>Manage Profile</CCardHeader>
                <CCardBody>
                    <CForm className="mt-2" onSubmit={handleSubmit}>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Name*</CFormLabel>
                                    <CFormInput name="name" className="col-4" type="text" defaultValue={user.name} required={true} />
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Email*</CFormLabel>
                                    <CFormInput name="email" className="col-4" type="email" defaultValue={user.email} required={true} />
                                </CInputGroup>
                            </CCol>
                            <CCol md="2" className="px-0">
                                {user.email && user.email_verified_at ?
                                    <i title="Verified" className="fa fa-check-circle text-success mt-2"></i> :
                                    <>
                                        <i title="Not verified" className="fa fa-exclamation-circle mt-2 text-warning"></i>
                                        <CButton className="mx-5" onClick={emailVerification}>Verify</CButton>
                                    </>

                                }
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Country Code*</CFormLabel>
                                    <CFormSelect name="country_code" aria-label="Country Code" defaultValue={user.country_code} required={true}>
                                        <option>Select Country</option>
                                        {
                                            countries && countries.map((country, index) =>
                                                <option key={index} value={`+${country.dial_code}`}>{`${country.name} (+${country.dial_code})`}</option>)
                                        }
                                    </CFormSelect>
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Phone Number*</CFormLabel>
                                    <CFormInput name="phone_number" className="col-4" type="text" defaultValue={user.phone_number} required={true} />
                                </CInputGroup>
                            </CCol>
                            <CCol md="2" className="px-0">
                                {user.phone_number && user.phone_verified_at ?
                                    <i title="Verified" className="fa fa-check-circle text-success mt-2"></i> :
                                    <>
                                        <i title="Not verified" className="fa fa-exclamation-circle mt-2 text-warning"></i>
                                        <CButton className="mx-5" onClick={verificationCode}>Verify</CButton>
                                    </>

                                }
                            </CCol>
                        </CRow>
                        <CRow className="mt-4 mx-2">
                            <CButton type="submit" color="primary" className="col-2">Submit</CButton>
                            <Link to="/#/" className="btn btn-danger col-2 mx-2">Cancel</Link>
                        </CRow>
                    </CForm>
                </CCardBody>
            </CCard>
            <CModal alignment="center" visible={visible} onClose={() => setVisible(false)}>
                <CForm className="mt-2" onSubmit={verifyPhoneNumber}>
                <CModalHeader>
                    <CModalTitle>Verify Phone Number</CModalTitle>
                </CModalHeader>
                <CModalBody>

                    <p>{`We have sent a verification code to ${user.country_code + user.phone_number}. Please check your whatsapp and enter the code below: `}</p>

                    <CFormLabel>Verification Code*</CFormLabel>
                    <CFormInput name="verification_code" type="text" required={true} />

                </CModalBody>
                <CModalFooter>
                    <CButton color="secondary" onClick={() => setVisible(false)}>
                        Cancel
                    </CButton>
                    <CButton type="submit" color="primary">Submit</CButton>
                </CModalFooter>
            </CForm>
            </CModal>
        </>
    )
}

export default Profile
