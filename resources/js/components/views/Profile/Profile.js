import React, {useEffect, useState} from 'react'

import {Link, useNavigate, useParams} from "react-router-dom";
import {
    CButton,
    CCard,
    CCardBody,
    CCardHeader,
    CCol,
    CForm, CFormCheck,
    CFormInput,
    CFormLabel, CFormSelect,
    CInputGroup, CModal, CModalBody, CModalFooter, CModalHeader, CModalTitle,
    CRow, CSpinner
} from "@coreui/react";
import fetchWrapper from "../../helpers/fetchWrapper";
import {swalConfirm, swalError, swalSuccess} from "../../helpers/common";
import {useDispatch, useSelector} from "react-redux";
import countries from "../../helpers/countries";
import CIcon from "@coreui/icons-react";
import {cilCheckCircle} from "@coreui/icons";


const Profile = () => {
    const navigate = useNavigate();
    const dispatch = useDispatch();

    const [user, setUser] = useState(useSelector(state => state.user));
    const [verifyData, setVerifyData] = useState({
        email: user.email,
        phone_number: user.phone_number,
        country_code: user.country_code,
    });

    const [visible, setVisible] = useState(false);
    const [emailLoading, setEmailLoading] = useState(false);
    const [phoneLoading, setPhoneLoading] = useState(false);
    const [verifyLoading, setVerifyLoading] = useState(false);

    const eventChange = (e) => {
        setVerifyData({...verifyData, [e.target.name]: e.target.value});
    }

    const updateUserData = (data) => {
        setUser(data.user);
        setVerifyData({
            email: data.user.email,
            phone_number: data.user.phone_number,
            country_code: data.user.country_code,
        })
        dispatch({type: 'set', user: data.user});
    }

    useEffect(() => {
        fetchWrapper.get('/api/user').then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                updateUserData(data)
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
        const whatsapp_notify = e.target.whatsapp_notify.checked;
        const email_notify = e.target.email_notify.checked;

        fetchWrapper.put('/api/profile', {
            name: name,
            email: email,
            country_code: country_code,
            phone_number: phone_number,
            whatsapp_notify: whatsapp_notify,
            email_notify: email_notify,
        }).then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                swalSuccess(data.message);
                updateUserData(data);
                navigate('/profile');
            } else {
                swalError(data.message);
            }
        }).catch((error) => {
            swalError("Error updating profile");
        });
    }

    const verificationCode = () => {
        if (verifyData.country_code && verifyData.phone_number) {
            setPhoneLoading(true);
            fetchWrapper.post('/api/verification-code', {
                country_code: verifyData.country_code,
                phone_number: verifyData.phone_number,
            }).then((response) => {
                const data = response.data;
                if (data.status === 'success') {
                    setVisible(true);
                } else {
                    swalError(data.message);
                }
            }).catch((error) => {
                swalError("Error sending verification code");
            }).finally(() => {
                setPhoneLoading(false);
            });
        } else {
            swalError("Please enter your phone number and country code");
        }
    }

    const verifyPhoneNumber = (e) => {
        setVerifyLoading(true);
        e.preventDefault();

        const verification_code = e.target.verification_code.value;

        fetchWrapper.post('/api/verify-phone-number', {
            verification_code: verification_code,
        }).then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                swalSuccess(data.message);
                updateUserData(data);
                setVisible(false);
                navigate('/profile');
            } else {
                swalError(data.message);
            }
        }).catch((error) => {
            swalError("Error verifying phone number");
        }).finally(() => {
            setVerifyLoading(false);
        });
    }

    const emailVerification = () => {
        if (verifyData.email) {
            setEmailLoading(true);
            fetchWrapper.post('/api/email-verification', {
                email: verifyData.email,
            }).then((response) => {
                const data = response.data;
                if (data.status === 'success') {
                    swalSuccess(data.message);
                } else {
                    swalError(data.message);
                }
            }).catch((error) => {
                swalError("Error sending email verification link");
            }).finally(() => {
                setEmailLoading(false);
            });
        } else {
            swalError("Please add your email address");
        }

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
                                    <CFormInput name="email" className="col-4" type="email" defaultValue={user.email} required={true} onChange={eventChange} />
                                </CInputGroup>
                            </CCol>
                            <CCol md="4" className="px-0 d-flex">
                                {user.email && user.email_verified_at ?
                                    <i title="Verified" className="fa fa-check-circle text-success mt-2"></i> :
                                    <>
                                        <i title="Not verified" className="fa fa-exclamation-circle mt-2 text-warning"></i>
                                        <CButton className="mx-5" onClick={emailVerification} disabled={emailLoading}>
                                            {emailLoading && <CSpinner component="span" size="sm" aria-hidden="true"/>} Verify
                                        </CButton>
                                    </>

                                }
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Country Code*</CFormLabel>
                                    <CFormSelect className="form-control" name="country_code" aria-label="Country Code" defaultValue={user.country_code} required={true} onChange={eventChange}>
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
                                    <CFormInput name="phone_number" className="col-4" type="text" defaultValue={user.phone_number} required={true} onChange={eventChange} />
                                </CInputGroup>
                            </CCol>
                            <CCol md="4" className="px-0 d-flex">
                                {user.phone_number && user.phone_verified_at ?
                                    <i title="Verified" className="fa fa-check-circle text-success mt-2"></i> :
                                    <>
                                        <i title="Not verified" className="fa fa-exclamation-circle mt-2 text-warning"></i>
                                        <CButton className="mx-5" onClick={verificationCode} disabled={phoneLoading}>
                                            {phoneLoading && <CSpinner component="span" size="sm" aria-hidden="true"/>} Verify
                                        </CButton>
                                    </>

                                }
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Notification Methods</CFormLabel>
                                    <CFormCheck name="whatsapp_notify" defaultChecked={user.notification_method?.whatsapp}></CFormCheck>
                                    <CFormLabel className="col-2">&nbsp;Whatsapp</CFormLabel>
                                    <CFormCheck name="email_notify" defaultChecked={user.notification_method?.email}></CFormCheck>
                                    <CFormLabel className="col-2">&nbsp;Email</CFormLabel>
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mt-4 mx-2">
                            <CButton type="submit" color="primary" className="col-2">Submit</CButton>
                            <Link to="/#/" className="btn btn-secondary col-2 mx-2">Cancel</Link>
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

                    <p>{`We have sent a verification code to ${verifyData.country_code + verifyData.phone_number}. Please check your whatsapp and enter the code below: `}</p>

                    <CFormLabel>Verification Code*</CFormLabel>
                    <CFormInput name="verification_code" type="text" required={true} />

                </CModalBody>
                <CModalFooter>
                    <CButton color="secondary" onClick={() => setVisible(false)}>
                        Cancel
                    </CButton>
                    <CButton type="submit" color="primary" disabled={verifyLoading}>
                        {verifyLoading && <CSpinner component="span" size="sm" aria-hidden="true"/>} Submit
                    </CButton>
                </CModalFooter>
            </CForm>
            </CModal>
        </>
    )
}

export default Profile
