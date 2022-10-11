import React from 'react'

import {Link, useNavigate} from "react-router-dom";
import {
    CButton,
    CCard,
    CCardBody,
    CCardHeader,
    CCol,
    CForm, CFormCheck,
    CFormInput,
    CFormLabel,
    CInputGroup,
    CRow
} from "@coreui/react";
import fetchWrapper from "../../helpers/fetchWrapper";
import {swalError, swalSuccess} from "../../helpers/common";


const ProjectCreate = () => {

    const navigate = useNavigate();

    const handleSubmit = (e) => {
        e.preventDefault();
        const project_name = e.target.project_name.value;
        const server_id = e.target.server_id.value;
        const channel_ids = e.target.channel_ids.value;
        const white_label_package = e.target.white_label_package.checked;

        fetchWrapper.post('/api/projects', {
            project_name: project_name,
            server_id: server_id,
            channel_ids: channel_ids,
            white_label_package: white_label_package
        }).then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                swalSuccess("Project created successfully");
                navigate('/projects');

            } else {
                swalError("Error creating project");
            }
        }).catch((error) => {
            swalError("Error creating project");
        });
    }

    return (
        <>
            <CCard>
                <CCardHeader>Create Project</CCardHeader>
                <CCardBody>
                    <CForm className="mt-2" onSubmit={handleSubmit}>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Project Name*</CFormLabel>
                                    <CFormInput name="project_name" className="col-4" type="text" required={true} />
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3 ">White Label Package</CFormLabel>
                                    <CFormCheck name="white_label_package"></CFormCheck>
                                </CInputGroup>
                            </CCol>
                        </CRow>

                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Server ID*</CFormLabel>
                                    <CFormInput name="server_id" className="col-4" type="text" required={true} />
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Channel IDs*</CFormLabel>
                                    <CFormInput name="channel_ids" className="col-4" type="text" required={true} />
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mt-4 mx-2">
                            <CButton type="submit" color="primary" className="col-2">Submit</CButton>
                            <Link to="/projects" className="btn btn-danger col-2 mx-2">Cancel</Link>
                        </CRow>
                    </CForm>
                </CCardBody>
            </CCard>

        </>
    )
}

export default ProjectCreate
